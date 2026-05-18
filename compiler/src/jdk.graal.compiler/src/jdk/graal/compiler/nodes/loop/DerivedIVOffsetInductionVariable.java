package jdk.graal.compiler.nodes.loop;

import java.util.Collection;

import jdk.graal.compiler.core.common.type.IntegerStamp;
import jdk.graal.compiler.core.common.type.Stamp;
import jdk.graal.compiler.debug.GraalError;
import jdk.graal.compiler.nodes.LogicNode;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.calc.AddNode;
import jdk.graal.compiler.nodes.calc.BinaryArithmeticNode;
import jdk.graal.compiler.nodes.calc.IntegerConvertNode;
import jdk.graal.compiler.nodes.calc.NegateNode;
import jdk.graal.compiler.nodes.calc.SubNode;
import jdk.graal.compiler.replacements.nodes.arithmetic.IntegerAddExactOverflowNode;
import jdk.graal.compiler.replacements.nodes.arithmetic.IntegerSubExactOverflowNode;
import jdk.graal.compiler.phases.common.util.LoopUtility;

public class DerivedIVOffsetInductionVariable extends DerivedInductionVariable {

    private final InductionVariable secondIV;
    private final BinaryArithmeticNode<?> value;
    private final boolean baseIsSubtrahend;

    public DerivedIVOffsetInductionVariable(Loop loop,
                                                     InductionVariable base,
                                                     InductionVariable secondIV,
                                                     BinaryArithmeticNode<?> value) {
        super(loop, base);
        this.secondIV = secondIV;
        this.value = value;
        this.baseIsSubtrahend = inferBaseIsSubtrahend(base, value);
    }

    private static boolean inferBaseIsSubtrahend(InductionVariable base,
                                                 BinaryArithmeticNode<?> value) {
        if (value instanceof AddNode) {
            return false;
        }
        if (value instanceof SubNode sub) {
            if (base.valueNode() == sub.getX()) {
                return false;
            }
            if (base.valueNode() == sub.getY()) {
                return true;
            }
        }
        throw GraalError.shouldNotReachHere(
                "Cannot infer baseIsSubtrahend for base=" + base + " value=" + value);
    }

    public InductionVariable getSecondIV() {
        return secondIV;
    }

    @Override
    public StructuredGraph graph() {
        return base.graph();
    }

    @Override
    public boolean structuralIntegrityValid() {
        return super.structuralIntegrityValid()
                && secondIV.structuralIntegrityValid()
                && value.isAlive();
    }

    // -----------------------------------------------------------------------
    // Direction
    // -----------------------------------------------------------------------

    @Override
    public Direction direction() {
        Direction baseDir = base.direction();
        Direction secondDir = secondIV.direction();
        if (baseDir == null || secondDir == null) {
            return null;
        }
        if (value instanceof AddNode) {
            if (baseDir == secondDir) {
                return baseDir;
            }
            return null;
        }
        if (value instanceof SubNode) {
            if (baseIsSubtrahend) {
                // result = secondIV - base
                if (secondDir == Direction.Up && baseDir == Direction.Down) {
                    return Direction.Up;
                }
                if (secondDir == Direction.Down && baseDir == Direction.Up) {
                    return Direction.Down;
                }
                return null;
            } else {
                // result = base - secondIV
                if (baseDir == Direction.Up && secondDir == Direction.Down) {
                    return Direction.Up;
                }
                if (baseDir == Direction.Down && secondDir == Direction.Up) {
                    return Direction.Down;
                }
                return null;
            }
        }
        return null;
    }

    // -----------------------------------------------------------------------
    // Value node
    // -----------------------------------------------------------------------

    @Override
    public ValueNode valueNode() {
        return value;
    }

    // -----------------------------------------------------------------------
    // Init
    // -----------------------------------------------------------------------

    @Override
    public ValueNode initNode() {
        return op(base.initNode(), secondIV.initNode());
    }

    @Override
    public boolean isConstantInit() {
        try {
            if (base.isConstantInit() && secondIV.isConstantInit()) {
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
        return opSafe(base.constantInit(), secondIV.constantInit());
    }

    // -----------------------------------------------------------------------
    // Stride
    // -----------------------------------------------------------------------

    @Override
    public ValueNode strideNode() {
        if (value instanceof SubNode && baseIsSubtrahend) {
            // result = secondIV - base
            // stride = stride(secondIV) - stride(base)
            return MathUtil.sub(graph(), secondIV.strideNode(), base.strideNode());
        }
        return op(base.strideNode(), secondIV.strideNode());
    }

    @Override
    public boolean isConstantStride() {
        try {
            if (base.isConstantStride() && secondIV.isConstantStride()) {
                constantStrideSafe();
                return true;
            }
        } catch (ArithmeticException e) {
            // overflow
        }
        return false;
    }

    @Override
    public long constantStride() {
        return constantStrideSafe();
    }

    private long constantStrideSafe() throws ArithmeticException {
        int bits = IntegerStamp.getBits(value.stamp(NodeView.DEFAULT));
        if (value instanceof AddNode) {
            return LoopUtility.addExact(bits,
                    base.constantStride(), secondIV.constantStride());
        }
        if (value instanceof SubNode) {
            if (baseIsSubtrahend) {
                return LoopUtility.subtractExact(bits,
                        secondIV.constantStride(), base.constantStride());
            }
            return LoopUtility.subtractExact(bits,
                    base.constantStride(), secondIV.constantStride());
        }
        throw GraalError.shouldNotReachHereUnexpectedValue(value);
    }

    // -----------------------------------------------------------------------
    // Extremum
    // -----------------------------------------------------------------------

    @Override
    public boolean isConstantExtremum() {
        try {
            if (base.isConstantExtremum() && secondIV.isConstantExtremum()) {
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
        return opSafe(base.constantExtremum(), secondIV.constantExtremum());
    }

    @Override
    public ValueNode extremumNode(boolean assumeLoopEntered, Stamp stamp) {
        return op(
                base.extremumNode(assumeLoopEntered, stamp),
                secondIV.extremumNode(assumeLoopEntered, stamp));
    }

    @Override
    public ValueNode extremumNode(boolean assumeLoopEntered, Stamp stamp,
                                  ValueNode maxTripCount) {
        return op(
                base.extremumNode(assumeLoopEntered, stamp, maxTripCount),
                secondIV.extremumNode(assumeLoopEntered, stamp, maxTripCount));
    }

    @Override
    protected ValueNode collectLocalExtremumOverflowConditions(boolean assumeLoopEntered,
                                                               Stamp stamp, ValueNode effectiveMaxTripCount, ValueNode baseExtremum,
                                                               Collection<LogicNode> conditions) {
        GraalError.guarantee(stamp instanceof IntegerStamp,
                "Expected integer stamp for %s but got %s", this, stamp);
        GraalError.guarantee(baseExtremum != null,
                "Expected base extremum for %s", this);

        ValueNode secondExtremum = secondIV.extremumNode(
                assumeLoopEntered, stamp, effectiveMaxTripCount);

        if (!secondExtremum.stamp(NodeView.DEFAULT).isCompatible(stamp)) {
            secondExtremum = IntegerConvertNode.convert(
                    secondExtremum, stamp, graph(), NodeView.DEFAULT);
        }

        if (value instanceof AddNode) {
            LogicNode addOverflow = IntegerAddExactOverflowNode.create(
                    baseExtremum, secondExtremum);
            if (!addOverflow.isContradiction()) {
                conditions.add(graph().addOrUniqueWithInputs(addOverflow));
            }
        } else {
            GraalError.guarantee(value instanceof SubNode,
                    "Expected add or sub for %s but got %s", this, value);
            if (baseIsSubtrahend) {
                LogicNode subOverflow = IntegerSubExactOverflowNode.create(
                        secondExtremum, baseExtremum);
                if (!subOverflow.isContradiction()) {
                    conditions.add(graph().addOrUniqueWithInputs(subOverflow));
                }
            } else {
                LogicNode subOverflow = IntegerSubExactOverflowNode.create(
                        baseExtremum, secondExtremum);
                if (!subOverflow.isContradiction()) {
                    conditions.add(graph().addOrUniqueWithInputs(subOverflow));
                }
            }
        }

        return op(baseExtremum, secondExtremum);
    }

    // -----------------------------------------------------------------------
    // Exit value
    // -----------------------------------------------------------------------

    @Override
    public ValueNode exitValueNode() {
        return op(base.exitValueNode(), secondIV.exitValueNode());
    }

    // -----------------------------------------------------------------------
    // Entry trip value
    // -----------------------------------------------------------------------

    @Override
    public ValueNode entryTripValue() {
        return op(base.entryTripValue(), secondIV.entryTripValue());
    }

    // -----------------------------------------------------------------------
    // Copy / duplicate support — required by DerivedInductionVariable
    // -----------------------------------------------------------------------

    @Override
    public ValueNode copyValue(InductionVariable newBase) {
        return copyValue(newBase, true);
    }

    @Override
    public ValueNode copyValue(InductionVariable newBase, boolean gvn) {
        return op(newBase.valueNode(), secondIV.valueNode(), gvn);
    }

    @Override
    public InductionVariable copy(InductionVariable newBase, ValueNode newValue) {
        if (newValue instanceof BinaryArithmeticNode<?> bin) {
            return new DerivedIVOffsetInductionVariable(
                    loop, newBase, secondIV, bin);
        }
        throw GraalError.shouldNotReachHere(
                "Unexpected newValue type: " + newValue);
    }

    // -----------------------------------------------------------------------
    // duplicate — required by DerivedInductionVariable
    // secondIV is kept as-is, only base is duplicated
    // -----------------------------------------------------------------------

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
    // isConstantScale / constantScale / offsetIsZero / offsetNode
    // required by InductionVariable for range check predication
    // -----------------------------------------------------------------------

    @Override
    public boolean isConstantScale(InductionVariable ref) {
        // Linear combination is scale=1 of itself
        if (this == ref) {
            return true;
        }
        // Delegate to base — if base is a constant scale of ref and
        // secondIV cancels out, this could still be constant scale,
        // but conservatively return false for the general case
        return false;
    }

    @Override
    public long constantScale(InductionVariable ref) {
        assert isConstantScale(ref);
        // Only valid when this == ref
        return 1;
    }

    @Override
    public boolean offsetIsZero(InductionVariable ref) {
        return this == ref;
    }

    @Override
    public ValueNode offsetNode(InductionVariable ref) {
        assert !offsetIsZero(ref);
        // Cannot express offset in terms of a single ref generically
        return null;
    }

    // -----------------------------------------------------------------------
    // Arithmetic helpers
    // -----------------------------------------------------------------------

    private long opSafe(long b, long s) throws ArithmeticException {
        int bits = IntegerStamp.getBits(value.stamp(NodeView.DEFAULT));
        if (value instanceof AddNode) {
            return LoopUtility.addExact(bits, b, s);
        }
        if (value instanceof SubNode) {
            if (baseIsSubtrahend) {
                // result = secondIV - base => s - b
                return LoopUtility.subtractExact(bits, s, b);
            }
            // result = base - secondIV => b - s
            return LoopUtility.subtractExact(bits, b, s);
        }
        throw GraalError.shouldNotReachHereUnexpectedValue(value);
    }

    public ValueNode op(ValueNode b, ValueNode s) {
        return op(b, s, true);
    }

    public ValueNode op(ValueNode b, ValueNode s, boolean gvn) {
        if (value instanceof AddNode) {
            return MathUtil.add(graph(), b, s, gvn);
        }
        if (value instanceof SubNode) {
            if (baseIsSubtrahend) {
                // result = secondIV - base => s - b
                return MathUtil.sub(graph(), s, b, gvn);
            }
            // result = base - secondIV => b - s
            return MathUtil.sub(graph(), b, s, gvn);
        }
        throw GraalError.shouldNotReachHereUnexpectedValue(value);
    }

    // -----------------------------------------------------------------------
    // Misc
    // -----------------------------------------------------------------------

    @Override
    public void deleteUnusedNodes() {
        // nothing owned exclusively by this IV
    }

    @Override
    public String toString(IVToStringVerbosity verbosity) {
        if (verbosity == IVToStringVerbosity.FULL) {
            return String.format(
                    "DerivedLinearCombinationIV base=(%s) %s second=(%s)",
                    base, value.getNodeClass().shortName(), secondIV);
        }
        return String.format("(%s) %s (%s)", base,
                value.getNodeClass().shortName(), secondIV);
    }
}