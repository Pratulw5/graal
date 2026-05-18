package jdk.graal.compiler.loop.phases;

import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.loop.InductionVariable;
import jdk.graal.compiler.nodes.loop.Loop;
import jdk.graal.compiler.nodes.loop.LoopPolicies;
import jdk.graal.compiler.nodes.loop.LoopsData;
import jdk.graal.compiler.nodes.spi.CoreProviders;
import jdk.graal.compiler.phases.common.CanonicalizerPhase;
import jdk.graal.compiler.nodes.loop.BasicInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedConvertedInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedOffsetInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedScaledInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedIVOffsetInductionVariable;
import jdk.graal.compiler.nodes.LoopExitNode;
import jdk.graal.compiler.nodes.ValueProxyNode;
import jdk.graal.compiler.nodes.loop.DerivedInductionVariable;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.FrameState;

public class LoopFoldingPhase extends LoopPhase<LoopPolicies> {

    public LoopFoldingPhase(CanonicalizerPhase canonicalizer, LoopPolicies policies) {
        super(policies, canonicalizer);
    }

    /**
     * Finds an existing ValueProxyNode for the given value at the given loop exit,
     * or creates a new one if none exists.
     */
    private ValueProxyNode getOrCreateProxy(ValueNode value, LoopExitNode loopExit,
                                            PhiNode phi, DebugContext debug) {
        for (Node usage : value.usages()) {
            if (usage instanceof ValueProxyNode vpn && vpn.proxyPoint() == loopExit) {
                return vpn;
            }
        }
        ValueProxyNode proxy = phi.graph().addWithoutUnique(
                new ValueProxyNode(value, loopExit));
        debug.log(DebugContext.INFO_LEVEL,
                "     [Proxy] Created proxy %s for value %s at exit %s",
                proxy, value, loopExit);
        return proxy;
    }

    /**
     * Tries to replace a PhiNode fed by a derived IV with a direct computation
     * using the live IV value proxied at the loop exit.
     *
     * Works uniformly for both counted and uncounted loops by proxying the live
     * base IV value at the loop exit — no need for extremumNode().
     */
    private void tryReplaceDerivedIVPhi(Loop loop, InductionVariable anyIv,
                                        DebugContext debug) {

        if (!(anyIv instanceof DerivedInductionVariable derivedIv)) {
            return;
        }

        for (Node usage : anyIv.valueNode().usages().snapshot()) {
            if (!(usage instanceof PhiNode phi)) {
                continue;
            }

            // Only replace if ALL non-FrameState, non-proxy usages of the phi are outside the loop
            boolean allOutside = true;
            for (Node phiUsage : phi.usages()) {
                if (phiUsage instanceof FrameState) continue;
                if (phiUsage instanceof ValueProxyNode) continue;
                if (!loop.isOutsideLoop(phiUsage)) {
                    allOutside = false;
                    break;
                }
            }
            if (!allOutside) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Skip] PhiNode %s has usages inside loop", phi);
                continue;
            }

            // Find the existing ValueProxyNode for this phi at the loop exit
            ValueProxyNode proxy = null;
            for (Node phiUsage : phi.usages()) {
                if (phiUsage instanceof ValueProxyNode vpn) {
                    proxy = vpn;
                    break;
                }
            }
            if (proxy == null) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Skip] No ValueProxyNode found for PhiNode %s", phi);
                continue;
            }

            LoopExitNode loopExit = proxy.proxyPoint();
            ValueNode exitValue = null;

            if (derivedIv instanceof DerivedIVOffsetInductionVariable linear) {
                // Proxy live values of both IVs at the loop exit
                ValueProxyNode baseProxy = getOrCreateProxy(
                        linear.getBase().valueNode(), loopExit, phi, debug);
                ValueProxyNode secondProxy = getOrCreateProxy(
                        linear.getSecondIV().valueNode(), loopExit, phi, debug);
                exitValue = phi.graph().addOrUniqueWithInputs(
                        linear.op(baseProxy, secondProxy));
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Linear] base proxy=%s  second proxy=%s  result=%s",
                        baseProxy, secondProxy, exitValue);

            } else {
                // For all other derived IVs, proxy the base IV's live value at exit
                ValueProxyNode baseProxy = getOrCreateProxy(
                        derivedIv.getBase().valueNode(), loopExit, phi, debug);

                if (derivedIv instanceof DerivedScaledInductionVariable scaled) {
                    exitValue = phi.graph().addOrUniqueWithInputs(
                            jdk.graal.compiler.nodes.loop.MathUtil.mul(
                                    phi.graph(), baseProxy, scaled.getScale()));
                    debug.log(DebugContext.INFO_LEVEL,
                            "     [Scaled] base proxy=%s  scale=%s  result=%s",
                            baseProxy, scaled.getScale(), exitValue);

                } else if (derivedIv instanceof DerivedOffsetInductionVariable offset) {
                    exitValue = phi.graph().addOrUniqueWithInputs(
                            offset.op(baseProxy, offset.getOffset()));
                    debug.log(DebugContext.INFO_LEVEL,
                            "     [Offset] base proxy=%s  offset=%s  result=%s",
                            baseProxy, offset.getOffset(), exitValue);

                } else if (derivedIv instanceof DerivedConvertedInductionVariable converted) {
                    exitValue = phi.graph().addOrUniqueWithInputs(
                            jdk.graal.compiler.nodes.calc.IntegerConvertNode.convert(
                                    baseProxy,
                                    converted.valueNode().stamp(NodeView.DEFAULT),
                                    phi.graph(),
                                    NodeView.DEFAULT));
                    debug.log(DebugContext.INFO_LEVEL,
                            "     [Converted] base proxy=%s  stamp=%s  result=%s",
                            baseProxy, converted.valueNode().stamp(NodeView.DEFAULT), exitValue);

                } else {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     [Skip] Unhandled derived IV type %s",
                            derivedIv.getClass().getSimpleName());
                    continue;
                }
            }

            if (exitValue == null) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Skip] exit value is null for %s", anyIv);
                continue;
            }

            proxy.replaceFirstInput(proxy.value(), exitValue);
            debug.log(DebugContext.INFO_LEVEL,
                    "     [Done] phi %s now fed by exit value %s", phi, exitValue);
        }
    }

    @Override
    protected void run(StructuredGraph graph, CoreProviders context) {
        if (graph.hasLoops()) {
            LoopsData data = context.getLoopsDataProvider().getLoopsData(graph);
            data.detectCountedLoops();

            DebugContext debug = graph.getDebug();

            for (Loop loop : data.loops()) {
                debug.log(DebugContext.INFO_LEVEL,
                        "  [Loop] %s  counted=%b  IVs=%d",
                        loop, loop.counted() != null, loop.getInductionVariables().size());

                for (InductionVariable anyIv : loop.getInductionVariables().getValues()) {
                    if (anyIv instanceof BasicInductionVariable) continue;

                    // Logging
                    if (anyIv instanceof DerivedIVOffsetInductionVariable linear) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Linear]    node=%s  base=%s  second=%s",
                                linear.valueNode(), linear.getBase().valueNode(),
                                linear.getSecondIV().valueNode());
                    } else if (anyIv instanceof DerivedScaledInductionVariable scaled) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Scaled]    node=%s  base=%s  scale=%s",
                                scaled.valueNode(), scaled.getBase().valueNode(), scaled.getScale());
                    } else if (anyIv instanceof DerivedOffsetInductionVariable offset) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Offset]    node=%s  base=%s  offset=%s",
                                offset.valueNode(), offset.getBase().valueNode(), offset.getOffset());
                    } else if (anyIv instanceof DerivedConvertedInductionVariable converted) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Converted] node=%s  base=%s",
                                converted.valueNode(), converted.getBase().valueNode());
                    }

                    tryReplaceDerivedIVPhi(loop, anyIv, debug);
                }
                debug.log(DebugContext.INFO_LEVEL,
                        "==================================================");
            }
        }
    }

    @Override
    public boolean checkContract() {
        return false;
    }
}