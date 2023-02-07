/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
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
     * Returns the formula without implicit all-quantification over the receiver object.
     */
    public Term getClause(ParsableVariable selfVar, TermServices services);

    public LabeledParserRuleContext getOriginalSpec();

    public InitiallyClause setKJT(KeYJavaType newKjt);


}
