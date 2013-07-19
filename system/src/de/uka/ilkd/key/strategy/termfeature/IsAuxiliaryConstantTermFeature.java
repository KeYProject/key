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
package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.AuxiliaryTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;


/**
 * A schema variable that is used as placeholder for auxiliary heap skolem
 * constants.
 */
public final class IsAuxiliaryConstantTermFeature extends BinaryTermFeature {

    public static final IsAuxiliaryConstantTermFeature INSTANCE =
            new IsAuxiliaryConstantTermFeature();


    private IsAuxiliaryConstantTermFeature() {
    }


    @Override
    protected boolean filter(Term t) {
        return t.hasLabels() &&
               t.containsLabel(AuxiliaryTermLabel.INSTANCE) &&
               t.op().arity() == 0 &&
               t.op() instanceof Function &&
               // the following is more or less a hack to match only on
               // skolem constants introduced by select-rules
               t.toString().startsWith("selectSK");

    }
}
