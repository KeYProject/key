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


import de.uka.ilkd.asmkey.logic.AsmLemma;
import de.uka.ilkd.asmkey.logic.AsmRule;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.op.MetaOperator;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;


/** Represents the environment necessary for parsing declarations. It
 * refines TermEnvironment.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public interface DeclarationEnvironment extends TermEnvironment, Named {

    /** Add the given sort to this environment.
     *
     * @throws EnvironmentException if sort already exists.
     */
    void addSort(Sort sort) throws EnvironmentException;

    /** Add schema variable declartion to this environment.
     *
     * @throws EnvironmentException if schema variable already exists.
     */
    void addSchemaVariable(SchemaVariable v) throws EnvironmentException;

    /** Add operator to this environment.
     *
     * @throws EnvironmentException if operator already exists.
     */
    void addOperator(Operator op) throws EnvironmentException;

    /** Replace operator to this environment.
     *
     * @throws EnvironmentException if operator already exists.
     */
    void replaceOperator(Operator op) throws EnvironmentException;

    /** Add a rule set to this environment.
     *
     * @throws EnvironmentException if the rule set already exists.
     */
    void addRuleSet(RuleSet h) throws EnvironmentException;

    /** Returns the rule set with the given name.
     *
     * @throws EnvironmentException if no such rule set exists.
     */
    RuleSet getRuleSet(Name id) throws EnvironmentException;

    /** Add Taclet declaration to this environment.
     *
     * @throws EnvironmentException if a taclet with the same name
     * already exists.
     */
    void addTaclet(Taclet t) throws EnvironmentException;

    /** Add rule (named ASM rule) to this environment.
     *
     * @throws EnvironmentException if proecdure with this name
     * already exists.
     */
    void addRule(AsmRule p) throws EnvironmentException;

    /** Add lemma (to be used in the proof) to this environment.
     *
     * @throws EnvironmentException if lemma with this name
     * already exists.
     */
    void addLemma(AsmLemma l) throws EnvironmentException;

    /** Add metaoperator
     *
     * @throws EnvironmentException if an op-like with this name
     * already exists.
     */
    void addMetaOperator(MetaOperator op) throws EnvironmentException;
}
