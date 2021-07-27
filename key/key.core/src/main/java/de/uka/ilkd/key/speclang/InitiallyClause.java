// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;


public interface InitiallyClause extends SpecificationElement {

    @Override
    public InitiallyClause map(UnaryOperator<Term> op, Services services);

    /**
     * Returns the formula without implicit all-quantification over
     * the receiver object.
     */
    public Term getClause(ParsableVariable selfVar, TermServices services);

    public LabeledParserRuleContext getOriginalSpec();

    public InitiallyClause setKJT(KeYJavaType newKjt);


}