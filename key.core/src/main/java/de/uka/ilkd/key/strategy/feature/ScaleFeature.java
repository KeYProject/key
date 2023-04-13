package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.util.Debug;

/**
 * A feature that applies an affine transformation to the result of a given feature. As a special
 * case, it can be used to scale the given feature.
 */
public abstract class ScaleFeature implements Feature {

    /** the base feature */
    private final Feature feature;

    protected ScaleFeature(Feature p_feature) {
        feature = p_feature;
    }

    /**
     * Create a feature that scales the result of the base feature.
     *
     * @param f the base feature
     * @param coeff the coefficient to be applied to the result of <code>f</code>
     */
    public static Feature createScaled(Feature f, double coeff) {
        return createAffine(f, coeff, 0);
    }

    /**
     * Create a feature that applies an affine transformation to the result of the base feature. The
     * transformation is described by a coefficient and an offset.
     *
     * @param f the base feature
     * @param coeff the coefficient to be applied to the result of <code>f</code>
     * @param offset the offset to be added to the result of <code>f</code> (after multiplication
     *        with <code>coeff</code>)
     */
    public static Feature createAffine(Feature f, double coeff, long offset) {
        return new MultFeature(f, coeff, offset);
    }

    /**
     * Create a feature that applies an affine transformation to the result of the base feature. The
     * transformation is described by two points in the domain and their images.
     *
     * @param f the base feature
     * @param dom0 point 0 in the domain
     * @param dom1 point 1 in the domain
     * @param img0 point 0 in the image
     * @param img1 point 1 in the image
     */
    public static Feature createAffine(Feature f, long dom0, long dom1,
            long img0, long img1) {
        Debug.assertFalse(dom0 == dom1,
            "Two different points are needed to define the " + "affine transformation");
        if (img0 == img1) {
            return ConstFeature.createConst(img0);
        }

        // now the two points of the domain (resp. of the image) are distinct

        if (dom0 == RuleAppCost.MAX_VALUE) {
            return firstDomInfty(f, dom1, img0, img1);
        } else {
            if (dom1 == RuleAppCost.MAX_VALUE) {
                return firstDomInfty(f, dom0, img1, img0);
            } else {

                // the points of the domain are finite
                if (img0 == RuleAppCost.MAX_VALUE) {
                    return firstImgInfty(f, dom0, dom1, img1);
                } else {
                    if (img1 == RuleAppCost.MAX_VALUE) {
                        return firstImgInfty(f, dom1, dom0, img0);
                    } else {
                        return realAffine(f, dom0, dom1, img0, img1);
                    }
                }

            }
        }
    }

    private static Feature firstDomInfty(Feature f, long dom1, long img0,
            long img1) {
        if (img0 == RuleAppCost.MAX_VALUE) {
            return createAffine(f, 1.0, img1 - dom1);
        } else {
            if (img1 == RuleAppCost.MAX_VALUE) {
                return ShannonFeature.createConditional(f, RuleAppCost.MAX_VALUE, img0,
                    RuleAppCost.MAX_VALUE);
            } else {
                return ShannonFeature.createConditional(f, RuleAppCost.MAX_VALUE, img0, img1);
            }
        }
    }

    private static Feature firstImgInfty(Feature f, long dom0, long dom1,
            long img1) {
        return ShannonFeature.createConditional(f, dom1, img1, RuleAppCost.MAX_VALUE);
    }

    public static Feature realAffine(Feature f, long dom0, long dom1,
            long img0, long img1) {

        final double coeff = (double) (img1 - img0) / (dom1 - dom0);
        final long offset = (long) (img0 - (dom0 * coeff));
        return createAffine(f, coeff, offset);
    }

    protected Feature getFeature() {
        return feature;
    }

    protected static boolean isZero(double p) {
        return Math.abs(p) < 0.0000001;
    }

    private static class MultFeature extends ScaleFeature {
        /** the coefficient */
        private final double coeff;
        /** the offset */
        private final long offset;

        private MultFeature(Feature f, double p_coeff, long p_offset) {
            super(f);
            if (p_offset == RuleAppCost.MAX_VALUE) {
                throw new IllegalArgumentException();
            }
            coeff = p_coeff;
            offset = p_offset;
        }

        public long computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
            final long cost = getFeature().computeCost(app, pos, goal);
            long costVal;

            if (cost == RuleAppCost.MAX_VALUE) {
                if (isZero(coeff)) {
                    costVal = 0;
                } else {
                    return RuleAppCost.MAX_VALUE;
                }
            } else {
                costVal = cost;
            }

            return (long) (coeff * costVal) + offset;
        }
    }

}
