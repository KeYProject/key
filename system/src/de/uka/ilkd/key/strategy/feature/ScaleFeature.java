// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.util.Debug;

/**
 * A feature that applies an affine transformation to the result of
 * a given feature.
 * As a special case, it can be used to scale the given feature.
 */
public abstract class ScaleFeature implements Feature {
 
    /** the base feature */
    private final Feature feature;
    
    protected ScaleFeature(Feature p_feature) {
        feature = p_feature;
    }

    /**
     * Create a feature that scales the result of the base feature.
     * @param f the base feature
     * @param coeff the coefficient to be applied to the result of 
     * <code>f</code>
     */
    public static Feature createScaled(Feature f, double coeff) {
        return createAffine(f, coeff, 0);
    }

    /**
     * Create a feature that applies an affine transformation to the result of
     * the base feature.
     * The transformation is described by a coefficient and an offset.
     * @param f the base feature
     * @param coeff the coefficient to be applied to the result of 
     * <code>f</code>
     * @param offset the offset to be added to the result of <code>f</code>
     * (after multiplication with <code>coeff</code>)
     */
    public static Feature createAffine(Feature f, double coeff, long offset) {
        return new MultFeature(f, coeff, offset);
    }

    /**
     * Create a feature that applies an affine transformation to the result of
     * the base feature.
     * The transformation is described by two points in the domain and their
     * images.
     * @param f the base feature
     * @param dom0 point 0 in the domain
     * @param dom1 point 1 in the domain
     * @param img0 point 0 in the image
     * @param img1 point 1 in the image
     */
    public static Feature createAffine(Feature f,
                                       RuleAppCost dom0, RuleAppCost dom1,
                                       RuleAppCost img0, RuleAppCost img1) {
        Debug.assertFalse ( dom0.equals ( dom1 ),
                            "Two different points are needed to define the "
                                                                                                                + "affine transformation" );
        if ( img0.equals(img1) )
            return ConstFeature.createConst ( img0 );
            
        // now the two points of the domain (resp. of the image) are distinct
        
        if ( dom0 instanceof TopRuleAppCost ) {
            return firstDomInfty ( f, dom1, img0, img1 );
        } else {
            if ( dom1 instanceof TopRuleAppCost )
                return firstDomInfty ( f, dom0, img1, img0 );
            else {
                
                // the points of the domain are finite
                if ( img0 instanceof TopRuleAppCost ) {
                    return firstImgInfty ( f, dom0, dom1, img1 );
                } else {
                    if ( img1 instanceof TopRuleAppCost )
                        return firstImgInfty ( f, dom1, dom0, img0 );
                    else {
                        return realAffine ( f, dom0, dom1, img0, img1 );
                    }
                }

            }
        }
    }
    
    private static Feature firstDomInfty (Feature f,
                                                            RuleAppCost dom1,
                                          RuleAppCost img0, RuleAppCost img1) {
        if ( img0 instanceof TopRuleAppCost ) {
            final long img1Val = getValue ( img1 );
            final long dom1Val = getValue ( dom1 );
            return createAffine ( f, 1.0, img1Val - dom1Val );
        } else {
            if ( img1 instanceof TopRuleAppCost )
                return ShannonFeature.createConditional ( f,
                                                          TopRuleAppCost.INSTANCE,
                                                          img0,
                                                          TopRuleAppCost.INSTANCE );
            else
                return ShannonFeature.createConditional ( f,
                                                          TopRuleAppCost.INSTANCE,
                                                          img0,
                                                          img1 );
        }
    }
    
    private static Feature firstImgInfty (Feature f,
                                          RuleAppCost dom0, RuleAppCost dom1,
                                                            RuleAppCost img1) {
        return ShannonFeature.createConditional ( f,
                                                  dom1,
                                                  img1,
                                                  TopRuleAppCost.INSTANCE );
    }

    public static Feature realAffine(Feature f,
                                     RuleAppCost dom0, RuleAppCost dom1,
                                     RuleAppCost img0, RuleAppCost img1) {
        final double img0Val = getValue ( img0 );
        final double img1Val = getValue ( img1 );
        final double dom0Val = getValue ( dom0 );
        final double dom1Val = getValue ( dom1 );

        final double coeff = ( img1Val - img0Val ) / ( dom1Val - dom0Val );
        final long offset = (long)( img0Val - ( dom0Val * coeff ) );
        return createAffine ( f, coeff, offset );
    }

    /**
     * @param cost
     */
    private static long getValue (RuleAppCost cost) {
        if ( !( cost instanceof LongRuleAppCost ) ) illegalCostError ( cost );
        return ( (LongRuleAppCost)cost ).getValue ();
    }

    protected static void illegalCostError (final RuleAppCost cost) {
        Debug.fail ( "Don't know what to do with cost class "
                     + cost.getClass () );
    }

    protected Feature getFeature () {
        return feature;
    }

    protected static boolean isZero (double p) {
        return Math.abs ( p ) < 0.0000001;
    }
    
    private static class MultFeature extends ScaleFeature {
        /** the coefficient */
        private final double coeff;
        /** the offset */
        private final long offset;

        private MultFeature (Feature f, double p_coeff, long p_offset) {
            super ( f );
            coeff = p_coeff;
            offset = p_offset;
        }

        public RuleAppCost compute (RuleApp app, PosInOccurrence pos, Goal goal) {
            final RuleAppCost cost = getFeature ().compute ( app, pos, goal );
            long costVal;
            
            if ( cost instanceof TopRuleAppCost ) {
                if ( isZero ( coeff ) )
                    costVal = 0;
                else
                    return TopRuleAppCost.INSTANCE;
            } else if ( cost instanceof LongRuleAppCost ) {
                costVal = ( (LongRuleAppCost)cost ).getValue ();
            } else {
                illegalCostError ( cost );
                return null;
            }

            return LongRuleAppCost.create ( (long)( coeff * costVal ) + offset );
        }
    }
    
}
