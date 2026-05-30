package jdk.graal.compiler.loop.phases;

import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.loop.DerivedIVScaledInductionVariable;
import jdk.graal.compiler.nodes.loop.InductionVariable;
import jdk.graal.compiler.nodes.loop.Loop;
import jdk.graal.compiler.nodes.loop.LoopPolicies;
import jdk.graal.compiler.nodes.loop.LoopsData;
import jdk.graal.compiler.nodes.loop.MathUtil;
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

    private ValueNode lastIterValue(BasicInductionVariable biv, LoopExitNode loopExit,
                                    Loop loop, PhiNode phi, DebugContext debug) {
        ValueProxyNode baseProxy = getOrCreateProxy(biv.getPhi(), loopExit, phi, debug);

        boolean isNormalExit = loop.counted() != null &&
                loopExit == loop.counted().getCountedExit();

        if (isNormalExit) {
            ValueNode stride = biv.strideNode();
            return phi.graph().addOrUniqueWithInputs(
                    MathUtil.sub(phi.graph(), baseProxy, stride));
        } else {
            return baseProxy;
        }
    }

    private void tryReplaceDerivedIVPhi(Loop loop, InductionVariable anyIv,
                                        DebugContext debug) {

        if (!(anyIv instanceof DerivedInductionVariable derivedIv)) {
            return;
        }

        for (Node usage : anyIv.valueNode().usages().snapshot()) {
            if (!(usage instanceof PhiNode phi)) {
                continue;
            }

            boolean allOutside = true;
            for (Node phiUsage : phi.usages()) {
                if (phiUsage instanceof FrameState) continue;
                if (phiUsage instanceof ValueProxyNode) continue;
                if (!loop.isOutsideLoop(phiUsage)) {
                    allOutside = false;
                    break;
                }
            }
            if (!allOutside) continue;

            ValueProxyNode proxy = null;
            for (Node phiUsage : phi.usages()) {
                if (phiUsage instanceof ValueProxyNode vpn) {
                    proxy = vpn;
                    break;
                }
            }
            if (proxy == null) continue;

            LoopExitNode loopExit = proxy.proxyPoint();

            BasicInductionVariable rootBiv = findRootBiv(derivedIv);
            if (rootBiv == null) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Skip] Cannot find root BasicIV for %s", derivedIv);
                continue;
            }

            ValueNode rootLastIter = lastIterValue(rootBiv, loopExit, loop, phi, debug);

            ValueNode exitValue = recomputeAtExit(derivedIv, rootBiv, rootLastIter,
                    loopExit, loop, phi, debug);

            if (exitValue == null) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Skip] Could not recompute exit value for %s", derivedIv);
                continue;
            }

            proxy.replaceFirstInput(proxy.value(), exitValue);
            debug.log(DebugContext.INFO_LEVEL,
                    "     [Done] phi %s → exit value %s  (rootBiv=%s rootLastIter=%s)",
                    phi, exitValue, rootBiv.valueNode(), rootLastIter);
        }
    }

    private static BasicInductionVariable findRootBiv(DerivedInductionVariable div) {
        InductionVariable base = div.getBase();
        while (base instanceof DerivedInductionVariable derived) {
            base = derived.getBase();
        }
        return base instanceof BasicInductionVariable biv ? biv : null;
    }

    private ValueNode recomputeAtExit(DerivedInductionVariable derivedIv,
                                      BasicInductionVariable rootBiv,
                                      ValueNode rootLastIter,
                                      LoopExitNode loopExit,
                                      Loop loop,
                                      PhiNode phi,
                                      DebugContext debug) {

        InductionVariable base = derivedIv.getBase();

        ValueNode baseLastIter;
        if (base instanceof BasicInductionVariable) {
            baseLastIter = rootLastIter;
        } else if (base instanceof DerivedInductionVariable derivedBase) {
            baseLastIter = recomputeAtExit(derivedBase, rootBiv, rootLastIter,
                    loopExit, loop, phi, debug);
            if (baseLastIter == null) return null;
        } else {
            return null;
        }

        if (derivedIv instanceof DerivedIVOffsetInductionVariable linear) {
            InductionVariable secondIV = linear.getSecondIV();
            ValueNode secondLastIter;

            if (secondIV instanceof BasicInductionVariable secondBiv) {
                if (secondBiv == rootBiv) {
                    secondLastIter = rootLastIter;
                } else {
                    secondLastIter = lastIterValue(secondBiv, loopExit, loop, phi, debug);
                }
            } else if (secondIV instanceof DerivedInductionVariable derivedSecond) {
                BasicInductionVariable secondRoot = findRootBiv(derivedSecond);
                if (secondRoot == rootBiv) {
                    secondLastIter = recomputeAtExit(derivedSecond, rootBiv, rootLastIter,
                            loopExit, loop, phi, debug);
                } else if (secondRoot != null) {
                    ValueNode secondRootLastIter = lastIterValue(secondRoot, loopExit, loop, phi, debug);
                    secondLastIter = recomputeAtExit(derivedSecond, secondRoot, secondRootLastIter,
                            loopExit, loop, phi, debug);
                } else {
                    return null;
                }
                if (secondLastIter == null) return null;
            } else {
                return null;
            }
            return phi.graph().addOrUniqueWithInputs(linear.op(baseLastIter, secondLastIter));

        } else if (derivedIv instanceof DerivedIVScaledInductionVariable ivScaled) {
            InductionVariable scaleIV = ivScaled.getScaleIV();
            ValueNode scaleLastIter;
            if (scaleIV instanceof BasicInductionVariable) {
                scaleLastIter = rootLastIter;
            } else if (scaleIV instanceof DerivedInductionVariable derivedScale) {
                scaleLastIter = recomputeAtExit(derivedScale, rootBiv, rootLastIter,
                        loopExit, loop, phi, debug);
                if (scaleLastIter == null) return null;
            } else {
                return null;
            }
            return phi.graph().addOrUniqueWithInputs(
                    MathUtil.mul(phi.graph(), baseLastIter, scaleLastIter));

        } else if (derivedIv instanceof DerivedScaledInductionVariable scaled) {
            return phi.graph().addOrUniqueWithInputs(
                    MathUtil.mul(phi.graph(), baseLastIter, scaled.getScale()));

        } else if (derivedIv instanceof DerivedOffsetInductionVariable offset) {
            return phi.graph().addOrUniqueWithInputs(
                    offset.op(baseLastIter, offset.getOffset()));

        } else if (derivedIv instanceof DerivedConvertedInductionVariable converted) {
            return phi.graph().addOrUniqueWithInputs(
                    jdk.graal.compiler.nodes.calc.IntegerConvertNode.convert(
                            baseLastIter,
                            converted.valueNode().stamp(NodeView.DEFAULT),
                            phi.graph(),
                            NodeView.DEFAULT));
        }

        debug.log(DebugContext.INFO_LEVEL,
                "     [Skip] Unhandled derived IV type %s",
                derivedIv.getClass().getSimpleName());
        return null;
    }

    @Override
    protected void run(StructuredGraph graph, CoreProviders context) {
        if (graph.hasLoops()) {
            LoopsData data = context.getLoopsDataProvider().getLoopsData(graph);
            data.detectCountedLoops();

            DebugContext debug = graph.getDebug();

            for (Loop loop : data.loops()) {
                boolean peeled = loop.loopBegin().peelings() > 0;
                if (!peeled) {
                    debug.log(DebugContext.INFO_LEVEL,
                            "  [Skip] Loop %s has not been peeled (peelings=%d), skipping",
                            loop, loop.loopBegin().peelings());
                    continue;
                }
                debug.log(DebugContext.INFO_LEVEL,
                        "  [Loop] %s  counted=%b  peeled=%b  peelings=%d  IVs=%d",
                        loop, loop.counted() != null, peeled,
                        loop.loopBegin().peelings(),
                        loop.getInductionVariables().size());

                for (InductionVariable anyIv : loop.getInductionVariables().getValues()) {
                    if (anyIv instanceof BasicInductionVariable) continue;
                    tryReplaceDerivedIVPhi(loop, anyIv, debug);
                }
            }
        }
    }

    @Override
    public boolean checkContract() {
        return false;
    }
}