package jdk.graal.compiler.nodes.loop;

import java.util.Collection;

import jdk.graal.compiler.core.common.type.IntegerStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.debug.GraalError;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.BinaryNode;
import jdk.graal.compiler.nodes.calc.IntegerConvertNode;
import jdk.graal.compiler.nodes.calc.LeftShiftNode;
import jdk.graal.compiler.nodes.calc.MulNode;
import jdk.graal.compiler.replacements.nodes.arithmetic.IntegerMulExactOverflowNode;
import jdk.graal.compiler.phases.common.util.LoopUtility;

/**
 * A derived induction variable of the form:
 *
 *   value = base * scaleIV   (MulNode)
 *   value = base << scaleIV  (LeftShiftNode where shift amount is an IV)
 *
 * Both base and scaleIV are induction variables of the same loop,
 * making this a nonlinear (quadratic) IV.
 */
public class DerivedIVScaledInductionVariable extends DerivedInductionVariable {

    private final InductionVariable scaleIV;

    /**
     * The actual graph node — either a MulNode or a LeftShiftNode.
     * Common parent is BinaryNode (ShiftNode extends BinaryNode,
     * MulNode extends BinaryArithmeticNode extends BinaryNode).
     */
    private final BinaryNode value;
    private final boolean isShift;

    public DerivedIVScaledInductionVariable(Loop loop,
                                            InductionVariable base,
                                            InductionVariable scaleIV,
                                            BinaryNode value) {
        super(loop, base);
        GraalError.guarantee(value instanceof MulNode || value instanceof LeftShiftNode,
                "DerivedIVScaledInductionVariable only supports MulNode or LeftShiftNode, got: %s",
                value.getClass().getSimpleName());
        this.scaleIV = scaleIV;
        this.value = value;
        this.isShift = value instanceof LeftShiftNode;
    }

    public InductionVariable getScaleIV() {
        return scaleIV;
    }

    // -----------------------------------------------------------------------
    // Core op helper — builds the right node type
    // -----------------------------------------------------------------------

    private ValueNode op(ValueNode b, ValueNode s) {
        return op(b, s, true);
    }

    private ValueNode op(ValueNode b, ValueNode s, boolean gvn) {
        if (isShift) {
            LeftShiftNode node = new LeftShiftNode(b, s);
            return gvn ? graph().addOrUniqueWithInputs(node) : node;
        }
        return MathUtil.mul(graph(), b, s, gvn);
    }

    // -----------------------------------------------------------------------
    // valueNode / graph / structuralIntegrityValid
    // -----------------------------------------------------------------------

    @Override
    public ValueNode valueNode() {
        return value;
    }

    @Override
    public StructuredGraph graph() {
        return base.graph();
    }

    @Override
    public boolean structuralIntegrityValid() {
        return super.structuralIntegrityValid()
                && scaleIV.structuralIntegrityValid()
                && value.isAlive();
    }

    // -----------------------------------------------------------------------
    // Direction — conservative null (nonlinear)
    // -----------------------------------------------------------------------

    @Override
    public Direction direction() {
        return null;
    }

    // -----------------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------------

    @Override
    public ValueNode initNode() {
        return op(base.initNode(), scaleIV.initNode());
    }

    @Override
    public boolean isConstantInit() {
        try {
            if (base.isConstantInit() && scaleIV.isConstantInit()) {
                constantInitSafe();
                return true;
            }
        } catch (ArithmeticException e) {
            // overflow
        }
        return false;
    }

    @Override
    public long constantInit() {
        return constantInitSafe();
    }

    private long constantInitSafe() throws ArithmeticException {
        return opSafe(base.constantInit(), scaleIV.constantInit());
    }

    // -----------------------------------------------------------------------
    // Stride — nonlinear, no constant stride
    // -----------------------------------------------------------------------

    @Override
    public ValueNode strideNode() {
        if (isShift) {
            // approximate: stride(base) << scaleIV
            return new LeftShiftNode(base.strideNode(), scaleIV.valueNode());
        }
        // product rule: stride(base)*scaleIV + base*stride(scaleIV)
        ValueNode term1 = MathUtil.mul(graph(), base.strideNode(), scaleIV.valueNode());
        ValueNode term2 = MathUtil.mul(graph(), base.valueNode(), scaleIV.strideNode());
        return MathUtil.add(graph(), term1, term2);
    }

    @Override
    public boolean isConstantStride() {
        return false;
    }

    @Override
    public long constantStride() {
        throw GraalError.shouldNotReachHere(
                "DerivedIVScaledInductionVariable has no constant stride — it is nonlinear");
    }

    // -----------------------------------------------------------------------
    // Extremum
    // -----------------------------------------------------------------------

    @Override
    public boolean isConstantExtremum() {
        try {
            if (base.isConstantExtremum() && scaleIV.isConstantExtremum()) {
                constantExtremumSafe();
                return true;
            }
        } catch (ArithmeticException e) {
            // overflow
        }
        return false;
    }

    @Override
    public long constantExtremum() {
        return constantExtremumSafe();
    }

    private long constantExtremumSafe() throws ArithmeticException {
        return opSafe(base.constantExtremum(), scaleIV.constantExtremum());
    }

    @Override
    public ValueNode extremumNode(boolean assumeLoopEntered, Stamp stamp) {
        return op(base.extremumNode(assumeLoopEntered, stamp),
                scaleIV.extremumNode(assumeLoopEntered, stamp));
    }

    @Override
    public ValueNode extremumNode(boolean assumeLoopEntered, Stamp stamp,
                                  ValueNode maxTripCount) {
        return op(base.extremumNode(assumeLoopEntered, stamp, maxTripCount),
                scaleIV.extremumNode(assumeLoopEntered, stamp, maxTripCount));
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

        ValueNode scaleExtremum = scaleIV.extremumNode(
                assumeLoopEntered, stamp, effectiveMaxTripCount);

        if (!scaleExtremum.stamp(NodeView.DEFAULT).isCompatible(stamp)) {
            scaleExtremum = IntegerConvertNode.convert(
                    scaleExtremum, stamp, graph(), NodeView.DEFAULT);
        }

        if (!isShift) {
            // Overflow check only meaningful for multiplication
            LogicNode mulOverflow = IntegerMulExactOverflowNode.create(
                    baseExtremum, scaleExtremum);
            if (!mulOverflow.isContradiction()) {
                conditions.add(graph().addOrUniqueWithInputs(mulOverflow));
            }
        }

        return op(baseExtremum, scaleExtremum);
    }

    // -----------------------------------------------------------------------
    // Exit / entry values
    // -----------------------------------------------------------------------

    @Override
    public ValueNode exitValueNode() {
        return op(base.exitValueNode(), scaleIV.exitValueNode());
    }

    @Override
    public ValueNode entryTripValue() {
        return op(base.entryTripValue(), scaleIV.entryTripValue());
    }

    // -----------------------------------------------------------------------
    // Copy / duplicate
    // -----------------------------------------------------------------------

    @Override
    public ValueNode copyValue(InductionVariable newBase) {
        return copyValue(newBase, true);
    }

    @Override
    public ValueNode copyValue(InductionVariable newBase, boolean gvn) {
        return op(newBase.valueNode(), scaleIV.valueNode(), gvn);
    }

    @Override
    public InductionVariable copy(InductionVariable newBase, ValueNode newValue) {
        if (newValue instanceof BinaryNode bin) {
            return new DerivedIVScaledInductionVariable(loop, newBase, scaleIV, bin);
        }
        throw GraalError.shouldNotReachHere(
                "Unexpected newValue type for DerivedIVScaledInductionVariable: "
                        + newValue.getClass().getSimpleName());
    }

    @Override
    public InductionVariable duplicate() {
        InductionVariable newBase = base.duplicate();
        return copy(newBase, copyValue(newBase, false));
    }

    @Override
    public InductionVariable duplicateWithNewInit(ValueNode newInit) {
        InductionVariable newBase = base.duplicateWithNewInit(newInit);
        return copy(newBase, copyValue(newBase, false));
    }

    // -----------------------------------------------------------------------
    // Scale / offset (conservative)
    // -----------------------------------------------------------------------

    @Override
    public boolean isConstantScale(InductionVariable ref) {
        return this == ref;
    }

    @Override
    public long constantScale(InductionVariable ref) {
        assert isConstantScale(ref);
        return 1;
    }

    @Override
    public boolean offsetIsZero(InductionVariable ref) {
        return this == ref;
    }

    @Override
    public ValueNode offsetNode(InductionVariable ref) {
        assert !offsetIsZero(ref);
        return null;
    }

    // -----------------------------------------------------------------------
    // Arithmetic helper
    // -----------------------------------------------------------------------

    private long opSafe(long b, long s) throws ArithmeticException {
        int bits = IntegerStamp.getBits(value.stamp(NodeView.DEFAULT));
        if (isShift) {
            if (s < 0 || s >= bits) {
                throw new ArithmeticException("Shift amount out of range: " + s);
            }
            return LoopUtility.multiplyExact(bits, b, 1L << s);
        }
        return LoopUtility.multiplyExact(bits, b, s);
    }

    // -----------------------------------------------------------------------
    // Misc
    // -----------------------------------------------------------------------

    @Override
    public void deleteUnusedNodes() {
        // nothing owned exclusively
    }

    @Override
    public String toString(IVToStringVerbosity verbosity) {
        String opSymbol = isShift ? "<<" : "*";
        if (verbosity == IVToStringVerbosity.FULL) {
            return String.format(
                    "DerivedIVScaledInductionVariable base=(%s) %s scaleIV=(%s)  node=%s",
                    base, opSymbol, scaleIV, value);
        }
        return String.format("(%s) %s (%s)", base, opSymbol, scaleIV);
    }
}