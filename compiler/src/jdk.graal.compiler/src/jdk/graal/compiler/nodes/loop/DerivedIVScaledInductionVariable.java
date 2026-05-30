package jdk.graal.compiler.nodes.loop;

import static jdk.graal.compiler.nodes.loop.MathUtil.mul;
import java.util.Collection;

import jdk.graal.compiler.core.common.type.IntegerStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.debug.GraalError;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.IntegerConvertNode;
import jdk.graal.compiler.nodes.util.GraphUtil;
import jdk.graal.compiler.replacements.nodes.arithmetic.IntegerMulExactOverflowNode;

/**
 * An induction variable of the form {@code base * scaleIV}, where both {@code base} and
 * {@code scaleIV} are themselves induction variables. Because the scale is not a loop-invariant
 * constant, many constant-folding operations are unavailable; they throw
 * {@link UnsupportedOperationException} rather than silently returning wrong answers.
 */
public class DerivedIVScaledInductionVariable extends DerivedInductionVariable {

    /**
     * The induction variable used as the scale factor. It must belong to the same loop (or an
     * enclosing loop) so that it is accessible at every iteration where {@code base} is live.
     */
    protected final InductionVariable scaleIV;

    /** The graph node that computes {@code base.valueNode() * scaleIV.valueNode()}. */
    protected final ValueNode value;

    // -------------------------------------------------------------------------
    // Construction
    // -------------------------------------------------------------------------


    /**
     * @param loop    the loop this IV belongs to
     * @param base    the base induction variable (what is being scaled)
     * @param scaleIV the induction variable acting as the scale factor
     * @param value   the pre-existing graph node representing {@code base * scaleIV}
     */
    public DerivedIVScaledInductionVariable(Loop loop,
                                            InductionVariable base,
                                            InductionVariable scaleIV,
                                            ValueNode value) {
        super(loop, base);
        this.scaleIV = scaleIV;
        this.value   = value;
    }

    public InductionVariable getScaleIV() {
        return scaleIV;
    }

    @Override
    public ValueNode valueNode() {
        return value;
    }

    // -------------------------------------------------------------------------
    // Structural integrity
    // -------------------------------------------------------------------------

    @Override
    public boolean structuralIntegrityValid() {
        return super.structuralIntegrityValid()
                && scaleIV.structuralIntegrityValid()
                && value.isAlive();
    }

    // -------------------------------------------------------------------------
    // Direction
    // -------------------------------------------------------------------------

    @Override
    public Direction direction() {
        return null;
    }

    // -----------------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------------

    @Override
    public ValueNode initNode() {
        // init = base.init * scaleIV.init
        return mul(graph(), base.initNode(), scaleIV.initNode());
    }

    @Override
    public ValueNode strideNode() {
        // stride is NOT simply base.stride * scaleIV.stride;
        // the product of two IVs is a quadratic expression, so we cannot
        // represent its stride as a simple linear value.  Return null to
        // signal "not a simple strided IV".
        return null;
    }

    // -------------------------------------------------------------------------
    // Constant-value queries  –  not supported when scale is an IV
    // -------------------------------------------------------------------------

    @Override
    public boolean isConstantInit() {
        return false;
    }

    @Override
    public boolean isConstantStride() {
        return false;
    }

    @Override
    public boolean isConstantExtremum() {
        return false;
    }

    @Override
    public long constantInit() {
        throw new UnsupportedOperationException(
                "constantInit() is not available for DerivedIVScaledInductionVariable " +
                        "because the scale is itself an induction variable.");
    }

    @Override
    public long constantStride() {
        throw new UnsupportedOperationException(
                "constantStride() is not available for DerivedIVScaledInductionVariable " +
                        "because the scale is itself an induction variable.");
    }

    @Override
    public long constantExtremum() {
        throw new UnsupportedOperationException(
                "constantExtremum() is not available for DerivedIVScaledInductionVariable " +
                        "because the scale is itself an induction variable.");
    }

    // -------------------------------------------------------------------------
    // Extremum nodes
    // -------------------------------------------------------------------------

    @Override
    public ValueNode extremumNode(boolean assumeLoopEntered, Stamp stamp) {
        ValueNode baseExtremum  = base.extremumNode(assumeLoopEntered, stamp);
        ValueNode scaleExtremum = IntegerConvertNode.convert(
                scaleIV.extremumNode(assumeLoopEntered, stamp), stamp, graph(), NodeView.DEFAULT);
        return mul(graph(), baseExtremum, scaleExtremum);
    }

    @Override
    public ValueNode extremumNode(boolean assumeLoopEntered, Stamp stamp, ValueNode maxTripCount) {
        ValueNode baseExtremum  = base.extremumNode(assumeLoopEntered, stamp, maxTripCount);
        ValueNode scaleExtremum = IntegerConvertNode.convert(
                scaleIV.extremumNode(assumeLoopEntered, stamp, maxTripCount),
                stamp, graph(), NodeView.DEFAULT);
        return mul(graph(), baseExtremum, scaleExtremum);
    }

    @Override
    protected ValueNode collectLocalExtremumOverflowConditions(boolean assumeLoopEntered,
                                                               Stamp stamp,
                                                               ValueNode effectiveMaxTripCount,
                                                               ValueNode baseExtremum,
                                                               Collection<LogicNode> conditions) {
        GraalError.guarantee(stamp instanceof IntegerStamp,
                "Expected integer stamp for %s but got %s", this, stamp);
        GraalError.guarantee(baseExtremum != null,
                "Expected base extremum for %s", this);

        // Convert the IV-scale extremum to the target stamp.
        ValueNode scaleExtremum = IntegerConvertNode.convert(
                scaleIV.extremumNode(assumeLoopEntered, stamp, effectiveMaxTripCount),
                stamp, graph(), NodeView.DEFAULT);

        LogicNode mulOverflow = IntegerMulExactOverflowNode.create(baseExtremum, scaleExtremum);
        if (!mulOverflow.isContradiction()) {
            conditions.add(graph().addOrUniqueWithInputs(mulOverflow));
        }

        return mul(graph(), baseExtremum, scaleExtremum);
    }

    // -----------------------------------------------------------------------
    // Exit / entry values
    // -----------------------------------------------------------------------

    @Override
    public ValueNode exitValueNode() {
        return mul(graph(), base.exitValueNode(), scaleIV.exitValueNode());
    }

    // -----------------------------------------------------------------------
    // Copy / duplicate
    // -----------------------------------------------------------------------

    @Override
    public void deleteUnusedNodes() {
        GraphUtil.tryKillUnused(scaleIV.valueNode());
    }

    // -------------------------------------------------------------------------
    // Scale / offset helpers
    // -------------------------------------------------------------------------

    /**
     * A constant scale can only be determined if the scaleIV itself has a constant scale
     * relative to {@code ref}, and the base also has a constant scale relative to {@code ref}.
     */
    @Override
    public boolean isConstantScale(InductionVariable ref) {
        // Both legs must be constant-scale for the product to be constant-scale.
        return scaleIV.isConstantScale(ref) && base.isConstantScale(ref);
    }

    @Override
    public long constantScale(InductionVariable ref) {
        assert isConstantScale(ref);
        return scaleIV.constantScale(ref) * base.constantScale(ref);
    }

    @Override
    public boolean offsetIsZero(InductionVariable ref) {
        if (super.offsetIsZero(ref)) {
            return true;
        }
        return base.offsetIsZero(ref);
    }

    @Override
    public ValueNode offsetNode(InductionVariable ref) {
        assert !offsetIsZero(ref);
        return null;
    }

    // -------------------------------------------------------------------------
    // Copy / clone support
    // -------------------------------------------------------------------------

    @Override
    public ValueNode copyValue(InductionVariable newBase, boolean gvn) {
        return MathUtil.mul(graph(), newBase.valueNode(), scaleIV.valueNode(), gvn);
    }

    @Override
    public ValueNode copyValue(InductionVariable newBase) {
        return copyValue(newBase, true);
    }

    @Override
    public InductionVariable copy(InductionVariable newBase, ValueNode newValue) {
        return new DerivedIVScaledInductionVariable(loop, newBase, scaleIV, newValue);
    }

    // -------------------------------------------------------------------------
    // Entry-trip value
    // -------------------------------------------------------------------------

    @Override
    public ValueNode entryTripValue() {
        return mul(graph(), base.entryTripValue(), scaleIV.entryTripValue());
    }

    // -------------------------------------------------------------------------
    // Debugging
    // -------------------------------------------------------------------------

    @Override
    public String toString(IVToStringVerbosity verbosity) {
        if (verbosity == IVToStringVerbosity.FULL) {
            return String.format("DerivedIVScaledInductionVariable base (%s) * scaleIV (%s)",
                    base, scaleIV);
        } else {
            return String.format("(%s) * (%s)", base, scaleIV);
        }
    }
}