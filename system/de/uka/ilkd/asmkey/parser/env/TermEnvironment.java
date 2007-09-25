// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.env;


import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;


/** This interface represents the environment (declarations) necessary
 * for parsing terms.
 *
 * @author Hubert Schmid
 */

public interface TermEnvironment extends SortEnvironment {

    /** Determines if a meta operator with the given name exists. */
    boolean containsMetaOp(Name id);

    /** Returns the meta operator with the given name.
     *
     * @throws EnvironmentException if no meta operator with the given
     * name exists.
     */
    MetaOperator getMetaOp(Name id) throws EnvironmentException;

    /** Determines if a sort with the given name exists. */
    boolean containsSchemaVariable(Name id);

    /** Returns the schema variable with the given name.
     *
     * @throws EnvironmentException if no such schema variable exists.
     */
    SchemaVariable getSchemaVariable(Name id) throws EnvironmentException;

    /** checks wether an operator with the given name exists.
     */
    boolean containsOperator(Name id);

    /** Returns the operator with the given name.
     *
     * @throws EnvironmentException if no such operator exists.
     */
    Operator getOperator(Name id) throws EnvironmentException;

    /** Returns the rule (named ASM ruls) with the given name.
     *
     * @throws EnvironmentException if no such rule exists.
     */
    AsmRule getRule(Name id) throws EnvironmentException;

    /** Returns the term which is abbreviated with name.
     *
     * @throws EnvironmentException if no such abbreviation exists.
     */
    Term getAbbreviatedTerm(String name) throws EnvironmentException;

    /** tells wether the environment serves to parse the body of a derived
     * function or not; important as {@link BigOperators} may only
     * appear in the body of such function.
     */
    boolean isParsingDerivedFunction();
}
