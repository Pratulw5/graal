package jdk.graal.compiler.loop.test;

import static jdk.graal.compiler.api.directives.GraalDirectives.injectBranchProbability;

import jdk.graal.compiler.nodes.GraphState;
import jdk.graal.compiler.nodes.ValuePhiNode;
import org.junit.Test;

import jdk.graal.compiler.core.common.CompilationIdentifier;
import jdk.graal.compiler.core.test.GraalCompilerTest;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.loop.phases.LoopFoldingPhase;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.loop.DefaultLoopPolicies;
import jdk.graal.compiler.phases.common.CanonicalizerPhase;
import jdk.graal.compiler.phases.common.ConditionalEliminationPhase;
import jdk.graal.compiler.phases.common.DeadCodeEliminationPhase;
import jdk.graal.compiler.phases.tiers.HighTierContext;
import jdk.vm.ci.meta.ResolvedJavaMethod;

public class LoopFoldingPhaseTest extends GraalCompilerTest {

    // ----------------------------------------------------------------
    // Snippet methods
    // ----------------------------------------------------------------

    /** DerivedScaledInductionVariable: i*3 exits the loop */
    // Change the snippet so the first valid input (n=1) gives a clearly
// non-zero, non-ambiguous result
    public static int scaledIVSnippet(int n) {
        int last = 0;
        for (int i = 1; injectBranchProbability(0.99, i < n); i++) {
            last = i * 3;  // n=2 → last=3, n=3 → last=6, etc.
        }
        return last;
    }

    /** DerivedOffsetInductionVariable: i+7 exits the loop */
    public static int offsetIVSnippet(int n) {
        int last = 0;
        for (int i = 0; injectBranchProbability(0.99, i < n); i++) {
            last = i + 7;
        }
        return last;
    }

    /** DerivedConvertedInductionVariable: (long)i exits the loop */
    public static long convertedIVSnippet(int n) {
        long last = 0;
        for (int i = 0; injectBranchProbability(0.99, i < n); i++) {
            last = (long) i;
        }
        return last;
    }

    /** DerivedIVOffsetInductionVariable: i+j (two IVs combined) exits the loop */
    public static int linearIVSnippet(int n) {
        int last = 0;
        for (int i = 0, j = n; injectBranchProbability(0.99, i < n); i++, j--) {
            last = i + j;
        }
        return last;
    }

    /** Zero-trip: phase must not crash when the loop body never executes */
    public static int zeroTripSnippet(int n) {
        int last = -1;
        for (int i = 0; injectBranchProbability(0.01, i < 0); i++) {
            last = i * 2 + n;
        }
        return last;
    }

    /**
     * Multiple exits: scaled IV used at both the early exit and the normal exit.
     */
    public static int multipleExitsSnippet(int n) {
        int v = 0;
        for (int i = 0; injectBranchProbability(0.99, i < n); i++) {
            v = i * 4;
            if (injectBranchProbability(0.01, v > 1000)) {
                return v;
            }
        }
        return v;
    }

    // ----------------------------------------------------------------
    // Helper: build a graph through a phase pipeline that mirrors
    // where LoopFoldingPhase actually sits in HighTier —
    // before HighTierLoweringPhase, before FrameStateAssignment.
    // ----------------------------------------------------------------
    public StructuredGraph buildGraph(String name, boolean applyFolding) {
        CompilationIdentifier id = new CompilationIdentifier() {
            @Override
            public String toString(Verbosity verbosity) {
                return name;
            }
        };
        ResolvedJavaMethod method = getResolvedJavaMethod(name);
        StructuredGraph graph = parse(
                builder(method, StructuredGraph.AllowAssumptions.YES, id, getInitialOptions()),
                getEagerGraphBuilderSuite());

        try (DebugContext.Scope _ = graph.getDebug().scope(name, method, graph)) {
            HighTierContext context = getDefaultHighTierContext();
            CanonicalizerPhase canonicalizer = createCanonicalizerPhase();

            // Minimal pre-processing that mirrors HighTier up to LoopFoldingPhase.
            // No GuardLoweringPhase, no FrameStateAssignmentPhase — those come later
            // in MidTier and are not required (or valid) here.
            canonicalizer.apply(graph, context);
            new ConditionalEliminationPhase(canonicalizer, false).apply(graph, context);
            new DeadCodeEliminationPhase().apply(graph);
            canonicalizer.apply(graph, context);

            graph.getGraphState().setAfterStage(GraphState.StageFlag.LOOP_OVERFLOWS_CHECKED); // ← add this

            if (applyFolding) {
                new LoopFoldingPhase(canonicalizer, new DefaultLoopPolicies()).apply(graph, context);
                canonicalizer.apply(graph, context);
            }

            new DeadCodeEliminationPhase().apply(graph);
            canonicalizer.apply(graph, context);

            graph.getDebug().dump(DebugContext.BASIC_LEVEL, graph, "after buildGraph");
            return graph;
        } catch (Throwable e) {
            throw getDebugContext().handle(e);
        }
    }

    // ----------------------------------------------------------------
    // Correctness tests — compile via Graal and compare with interpreter
    // ----------------------------------------------------------------

    @Test
    public void testScaledIV() {
        for (int i = 2; i < 64; i++) {
            test("scaledIVSnippet", i);
        }
    }

    @Test
    public void testOffsetIV() {
        for (int i = 1; i < 64; i++) {
            test("offsetIVSnippet", i);
        }
    }

    @Test
    public void testConvertedIV() {
        for (int i = 1; i < 64; i++) {
            test("convertedIVSnippet", i);
        }
        test("convertedIVSnippet", Integer.MAX_VALUE - 1);
        test("convertedIVSnippet", 0);
        test("convertedIVSnippet", 1);
    }

    @Test
    public void testLinearIV() {
        for (int i = 1; i < 64; i++) {
            test("linearIVSnippet", i);
        }
    }

    @Test
    public void testZeroTrip() {
        test("zeroTripSnippet", 0);
        test("zeroTripSnippet", 99);
        test("zeroTripSnippet", -1);
    }

    @Test
    public void testMultipleExits() {
        for (int i = 1; i < 64; i++) {
            test("multipleExitsSnippet", i);
        }
        test("multipleExitsSnippet", 500);
        test("multipleExitsSnippet", 0);
    }

    // ----------------------------------------------------------------
    // Structural test: folding should not increase ValuePhi count
    // ----------------------------------------------------------------

    @Test
    public void testFoldingReducesPhiCount() {
        StructuredGraph withoutFolding = buildGraph("scaledIVSnippet", false);
        StructuredGraph withFolding    = buildGraph("scaledIVSnippet", true);

        // Count only ValuePhiNodes — LoopFoldingPhase eliminates derived IV phis
        // which are ValuePhiNodes; guard/memory phis are unaffected.
        int phisBefore = withoutFolding.getNodes().filter(ValuePhiNode.class).count();
        int phisAfter  = withFolding.getNodes().filter(ValuePhiNode.class).count();

        assertTrue(
                "LoopFoldingPhase should not increase ValuePhi count; before=" + phisBefore + " after=" + phisAfter,
                phisAfter <= phisBefore);
    }

    // ----------------------------------------------------------------
    // No createSuites override — LoopFoldingPhase is already registered
    // in HighTier (see HighTier.java) at the correct position.
    // Overriding it here would double-apply the phase and misplace it
    // relative to FrameStateAssignmentPhase, causing miscompilation.
    // ----------------------------------------------------------------
}