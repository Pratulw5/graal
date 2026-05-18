package jdk.graal.compiler.loop.phases;
import jdk.graal.compiler.nodes.PhiNode;
import jdk.graal.compiler.graph.Node;
import jdk.graal.compiler.debug.DebugContext;
import jdk.graal.compiler.nodes.StructuredGraph;
import jdk.graal.compiler.nodes.ValueNode;
import jdk.graal.compiler.nodes.loop.CountedLoopInfo;
import jdk.graal.compiler.nodes.loop.InductionVariable;
import jdk.graal.compiler.nodes.loop.Loop;
import jdk.graal.compiler.nodes.loop.LoopPolicies;
import jdk.graal.compiler.nodes.loop.LoopsData;
import jdk.graal.compiler.nodes.spi.CoreProviders;
import jdk.graal.compiler.phases.common.CanonicalizerPhase;
import jdk.graal.compiler.nodes.NodeView;
import jdk.graal.compiler.nodes.loop.BasicInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedConvertedInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedOffsetInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedScaledInductionVariable;
import jdk.graal.compiler.nodes.loop.DerivedLinearCombinationInductionVariable;
import jdk.graal.compiler.nodes.LoopExitNode;
import jdk.graal.compiler.nodes.ValuePhiNode;
import jdk.graal.compiler.nodes.ValueProxyNode;
import jdk.graal.compiler.nodes.loop.DerivedInductionVariable;
import jdk.graal.compiler.nodes.FrameState;

public class LoopFoldingPhase extends LoopPhase<LoopPolicies> {

    public LoopFoldingPhase(CanonicalizerPhase canonicalizer, LoopPolicies policies) {
        super(policies, canonicalizer);
    }

    /**
     * Finds or creates a ValueProxyNode for the given value at the given loop exit.
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
                "     [Replace] Created new proxy %s for value %s at exit %s",
                proxy, value, loopExit);
        return proxy;
    }

    /**
     * Tries to replace the PhiNode fed by a derived IV with a post-loop computation using
     * the extremum (last body value) of the loop-controlling base IV.
     *
     * This only applies when the root base IV of the derived IV is the loop-controlling IV
     * (limitCheckedIV), because only then do we know the extremum precisely.
     *
     * We use the extremum — the value of the IV in the last loop body execution — rather than
     * the exit value, because the inner code runs only during the last body iteration, not after
     * the loop condition exits.
     */
    private void tryReplaceDerivedIVPhi(Loop loop, InductionVariable anyIv,
                                        InductionVariable limitCheckedIV,
                                        DebugContext debug) {

        if (!(anyIv instanceof DerivedInductionVariable derivedIv)) {
            return;
        }

        // Only handle derived IVs whose root base is the loop-controlling IV.
        // Walk up the base chain to find the root basic IV.
        InductionVariable rootIv = derivedIv.getRootIV();
        if (rootIv != limitCheckedIV) {
            debug.log(DebugContext.INFO_LEVEL,
                    "     [Replace] Skipping derived IV %s — root IV %s is not the limit-checked IV %s",
                    anyIv.valueNode(), rootIv.valueNode(), limitCheckedIV.valueNode());
            return;
        }

        for (Node usage : anyIv.valueNode().usages().snapshot()) {
            if (!(usage instanceof PhiNode phi)) {
                continue;
            }

            boolean allOutside = true;
            for (Node phiUsage : phi.usages()) {
                if (phiUsage instanceof FrameState) {
                    continue;
                }
                if (phiUsage instanceof ValueProxyNode) {
                    continue;
                }
                if (!loop.isOutsideLoop(phiUsage)) {
                    allOutside = false;
                    break;
                }
            }
            if (!allOutside) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Replace] PhiNode %s skipped — has usages inside loop", phi);
                continue;
            }

            ValueProxyNode proxy = null;
            for (Node phiUsage : phi.usages()) {
                if (phiUsage instanceof ValueProxyNode vpn) {
                    proxy = vpn;
                    break;
                }
            }

            if (proxy == null) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Replace] No ValueProxyNode found for PhiNode %s — skipping", phi);
                continue;
            }

            LoopExitNode loopExit = proxy.proxyPoint();

            // Use the extremum of the base IV (value at last body iteration),
            // not the exit value (which is the value after the loop condition fires).
            // The inner code only executes during the last body iteration.
            CountedLoopInfo countedInfo = loop.counted();
            ValueNode exitValue = null;

            if (derivedIv instanceof DerivedLinearCombinationInductionVariable linear) {
                // Both base IVs must be rooted in the limit-checked IV (already guaranteed above
                // for the outer derivedIv; check the second IV's root too).
                InductionVariable secondRootIv = linear.getSecondIV().getRootIV();
                if (secondRootIv != limitCheckedIV) {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     [Replace] Linear combination second IV root %s is not limit-checked IV — skipping",
                            secondRootIv.valueNode());
                    continue;
                }

                // Extremum of the base IV in the stamp of the base IV node.
                ValueNode baseExtremum = linear.getBase().extremumNode(
                        false, linear.getBase().valueNode().stamp(NodeView.DEFAULT));
                ValueNode secondExtremum = linear.getSecondIV().extremumNode(
                        false, linear.getSecondIV().valueNode().stamp(NodeView.DEFAULT));

                ValueProxyNode baseProxy = getOrCreateProxy(baseExtremum, loopExit, phi, debug);
                ValueProxyNode secondProxy = getOrCreateProxy(secondExtremum, loopExit, phi, debug);

                exitValue = phi.graph().addOrUniqueWithInputs(
                        linear.op(baseProxy, secondProxy));

                debug.log(DebugContext.INFO_LEVEL,
                        "     [Replace] Linear combination: base extremum proxy=%s second extremum proxy=%s result=%s",
                        baseProxy, secondProxy, exitValue);

            } else {
                // Extremum of the direct base IV.
                ValueNode baseExtremum = derivedIv.getBase().extremumNode(
                        false, derivedIv.getBase().valueNode().stamp(NodeView.DEFAULT));

                debug.log(DebugContext.INFO_LEVEL,
                        "     [Replace] Using base extremum %s (last body value) for derived IV %s",
                        baseExtremum, anyIv.valueNode());

                ValueProxyNode baseProxy = getOrCreateProxy(baseExtremum, loopExit, phi, debug);

                if (derivedIv instanceof DerivedScaledInductionVariable scaled) {
                    exitValue = phi.graph().addOrUniqueWithInputs(
                            jdk.graal.compiler.nodes.loop.MathUtil.mul(
                                    phi.graph(), baseProxy, scaled.getScale()));

                } else if (derivedIv instanceof DerivedOffsetInductionVariable offset) {
                    exitValue = phi.graph().addOrUniqueWithInputs(
                            offset.op(baseProxy, offset.getOffset()));

                } else if (derivedIv instanceof DerivedConvertedInductionVariable converted) {
                    exitValue = phi.graph().addOrUniqueWithInputs(
                            jdk.graal.compiler.nodes.calc.IntegerConvertNode.convert(
                                    baseProxy,
                                    converted.valueNode().stamp(NodeView.DEFAULT),
                                    phi.graph(),
                                    NodeView.DEFAULT));

                } else {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     [Replace] Unhandled derived IV type %s — skipping",
                            derivedIv.getClass().getSimpleName());
                    continue;
                }
            }

            if (exitValue == null) {
                debug.log(DebugContext.INFO_LEVEL,
                        "     [Replace] exit value computation returned null for %s — skipping",
                        anyIv);
                continue;
            }

            debug.log(DebugContext.INFO_LEVEL,
                    "     [Replace] Replacing proxy input with last-body-iteration value %s", exitValue);
            proxy.replaceFirstInput(proxy.value(), exitValue);
            debug.log(DebugContext.INFO_LEVEL,
                    "     [Replace] Done — phi %s now fed by last-body-iteration value %s", phi, exitValue);
        }
    }

    @Override
    protected void run(StructuredGraph graph, CoreProviders context) {

        if (graph.hasLoops()) {
            LoopsData data = context.getLoopsDataProvider().getLoopsData(graph);
            data.detectCountedLoops();

            DebugContext debug = graph.getDebug();

            for (Loop loop : data.countedLoops()) {
                CountedLoopInfo countedInfo = loop.counted();
                if (countedInfo == null) {
                    continue;
                }

                debug.log(DebugContext.INFO_LEVEL, "==================================================");
                debug.log(DebugContext.INFO_LEVEL,
                        "[LoopFolding] Inspecting Loop: %s", loop.getCFGLoop().getHeader());

                InductionVariable iv = countedInfo.getLimitCheckedIV();
                debug.log(DebugContext.INFO_LEVEL, "  -> Primary IV: %s", iv.valueNode());
                debug.log(DebugContext.INFO_LEVEL, "     Direction:  %s", iv.direction());
                debug.log(DebugContext.INFO_LEVEL, "     Stride:     %s", iv.strideNode());
                debug.log(DebugContext.INFO_LEVEL, "     Init:       %s", iv.initNode());
                debug.log(DebugContext.INFO_LEVEL, "     Limit:      %s", countedInfo.getLimit());
                debug.log(DebugContext.INFO_LEVEL, "     Exit Value: %s", countedInfo.getBodyIVExitValue());

                if (countedInfo.loopCanNeverOverflow()) {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     Extremum:   %s", countedInfo.getBodyIVExtremum());
                } else {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     Extremum:   (skipped — overflow not ruled out)");
                }
                if (countedInfo.isConstantMaxTripCount()) {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     Trip Count: %s (constant)", countedInfo.constantMaxTripCount());
                } else if (countedInfo.loopCanNeverOverflow()) {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     Trip Count: %s (dynamic)", countedInfo.maxTripCountNode());
                } else {
                    debug.log(DebugContext.INFO_LEVEL,
                            "     Trip Count: (skipped — overflow not ruled out)");
                }

                debug.log(DebugContext.INFO_LEVEL, "  -> Derived IVs:");
                for (InductionVariable anyIv : loop.getInductionVariables().getValues()) {
                    if (anyIv == iv) {
                        continue;
                    }
                    if (anyIv instanceof BasicInductionVariable) {
                        continue;
                    }

                    // Logging
                    if (anyIv instanceof DerivedLinearCombinationInductionVariable linear) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Linear]    node=%s  base=%s  second=%s  stride=%s  init=%s  direction=%s",
                                linear.valueNode(),
                                linear.getBase().valueNode(),
                                linear.getSecondIV().valueNode(),
                                linear.strideNode(),
                                linear.initNode(),
                                linear.direction());

                    } else if (anyIv instanceof DerivedScaledInductionVariable scaled) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Scaled]    node=%s  base=%s  scale=%s  stride=%s  init=%s  direction=%s",
                                scaled.valueNode(),
                                scaled.getBase().valueNode(),
                                scaled.getScale(),
                                scaled.strideNode(),
                                scaled.initNode(),
                                scaled.direction());

                    } else if (anyIv instanceof DerivedOffsetInductionVariable offset) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Offset]    node=%s  base=%s  offset=%s  stride=%s  init=%s  direction=%s",
                                offset.valueNode(),
                                offset.getBase().valueNode(),
                                offset.getOffset(),
                                offset.strideNode(),
                                offset.initNode(),
                                offset.direction());

                    } else if (anyIv instanceof DerivedConvertedInductionVariable converted) {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Converted] node=%s  base=%s  stamp=%s  stride=%s  init=%s  direction=%s",
                                converted.valueNode(),
                                converted.getBase().valueNode(),
                                converted.valueNode().stamp(NodeView.DEFAULT),
                                converted.strideNode(),
                                converted.initNode(),
                                converted.direction());

                    } else {
                        debug.log(DebugContext.INFO_LEVEL,
                                "     [Unknown]   node=%s  type=%s",
                                anyIv.valueNode(),
                                anyIv.getClass().getSimpleName());
                    }

                    // Phi usage logging
                    for (Node usageNode : anyIv.valueNode().usages()) {
                        if (usageNode instanceof ValueProxyNode) {
                            continue;
                        }
                        if (usageNode instanceof PhiNode phi) {
                            debug.log(DebugContext.INFO_LEVEL,
                                    "        -> used by PhiNode: %s  valueCount=%d",
                                    phi, phi.valueCount());
                            for (Node phiUsage : phi.usages()) {
                                debug.log(DebugContext.INFO_LEVEL,
                                        "           -> PhiNode used by: %s  type=%s",
                                        phiUsage, phiUsage.getClass().getSimpleName());
                            }
                        }
                    }

                    // Pass limitCheckedIV so we only transform derived IVs rooted in it,
                    // and use extremumNode (last body value) instead of exitValueNode.
                    tryReplaceDerivedIVPhi(loop, anyIv, iv, debug);
                }
                debug.log(DebugContext.INFO_LEVEL, "==================================================");
            }
        }
    }

    @Override
    public boolean checkContract() {
        return false;
    }
}