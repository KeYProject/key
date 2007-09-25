// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden  
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.asmkey.proof.init;

import java.util.HashMap;

import de.uka.ilkd.asmkey.unit.Unit;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.ldt.BooleanLDT;
import de.uka.ilkd.key.logic.ldt.LDT;
import de.uka.ilkd.key.logic.ldt.IntegerLDT;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.ModStrategy;

/** 
 * an instance of this class describes the initial configuration of the prover.
 * This includes sorts, functions, heuristics, and variables namespaces, 
 * information on the underlying java model, and a set of rules.
 *
 * this class is an adaptation of the original key file with the appropriate
 * java and number model (NO_MODEL and math arith).
 *
 * attempt to change them will raise an exception.
 *
 * @author Stanislas Nanchen
 */
public class InitConfig extends de.uka.ilkd.key.proof.init.InitConfig {

    private IntegerLDT intLDT = null; //new AsmIntegerLDT();

    private BooleanLDT booleanLDT = null; //new AsmBooleanLDT();

    private LDT[] ldts = new LDT[] { booleanLDT, intLDT };
    
    private Services services = new Services();

    //private Choice defaultChoice = new Choice(new Name("Default"));

    private Unit unit;

    private SetOfChoice activatedChoices = SetAsListOfChoice.EMPTY_SET;

    private HashMap category2DefaultChoice = new HashMap();

    public InitConfig(Unit unit) {
	super();
	this.unit = unit;
    }

    public void setNamespaces(NamespaceSet nss) {
	throw new InitConfigException("AsmKeY: setNamespaces forbidden in AsmKeY.");
    }
    
    public void setServices(Services serv) {
	throw new InitConfigException("AsmKeY: Java Services may not be changed in AsmKeY.");
    }

    public void setDefaultChoice(Choice defaultChoice){
	throw new InitConfigException("AsmKeY: the default Choice may not be changed in AsmKeY.");
    }

    public Choice getDefaultChoice(){
	return null;
    }

    public Services getServices() {
	return services;
    }

    /** returns the HashMap that maps categories to their default choices */
    public HashMap getCategory2DefaultChoice(){
	return category2DefaultChoice;
    }

    public void setCategory2DefaultChoice(HashMap category2DefaultChoice){
	throw new InitConfigException("AsmKeY: the category2DefaultChoice map may not be changed in AsmKeY");
    } 

    public void addCategory2DefaultChoices(HashMap init){ 
	throw new InitConfigException("AsmKeY: the category2DefaultChoice may not have new elements added to.");
    }

    public void setActivatedChoices(SetOfChoice activatedChoices) {
	throw new InitConfigException("AsmKeY: the activatedChoices may not be changed in AsmKeY");
    }

    public SetOfChoice getActivatedChoices(){
	return activatedChoices;
    }

    /* namespaces */
    public NamespaceSet namespaces() {
	return new NamespaceSet(unit.varNS(), unit.funcNS(),
				unit.sortNS(), unit.ruleSetNS(),
				unit.choiceNS(), unit.progVarNS());
    }

    /* java info */
    public JavaInfo javaInfo() {
	return services.getJavaInfo();
    }

    /** init the int ldt
     */
    public IntegerLDT initIntegerLDT() {
        /*try {
            intLDT.init(env.funcNS(), env.getSort(new Name("int")),
                        SLListOfType.EMPTY_LIST.append(PrimitiveType.JAVA_INT));
            return intLDT;
        } catch (EnvironmentException ee) {
            ee.printStackTrace(System.err);
            System.exit(1);
	    }*/
        return null;
    }

    /** init the boolean ldt 
     */
    public BooleanLDT initBooleanLDT() {
	//TODO
        return null;
    }

    public LDT[] ldtModels(){
	return ldts;
    }
    
    /** returns the function namespace of this initial configuration
     */
    public Namespace funcNS() {
	if (unit != null) { return unit.funcNS(); } else { return super.funcNS(); }
    }

    /** returns the sort namespace of this initial configuration
     */
    public Namespace sortNS() {
	if(unit != null) { return unit.sortNS(); } else { return super.sortNS(); }
    }

    /** returns the heuristics namespace of this initial configuration
     */
    public Namespace ruleSetNS() {
	if(unit != null) { return unit.ruleSetNS(); } else { return super.ruleSetNS(); }
    }

    /** returns the variable namespace of this initial configuration
     */
    public Namespace varNS() {
	if(unit != null) { return unit.varNS(); } else { return super.varNS(); }
    }

    /** returns the program variable namespace of this initial configuration
     */
    public Namespace progVarNS() {
	if(unit != null) { return unit.progVarNS(); } else { return super.progVarNS(); }
    }

    /** returns the choice namespace of this initial configuration
     */
    public Namespace choiceNS() {
	if(unit != null) { return unit.choiceNS(); } else { return super.choiceNS(); }
    }

    public void add(NamespaceSet ns, ModStrategy mod) {
	throw new InitConfigException("AsmKeY: you may not add new namespaces.");
    }

    /** return the asmkey environment (namespaces)
     */
    public Unit unit() {
	return unit;
    }

    /** returns a newly created taclet index for the set of activated 
     * taclets contained in this initial configuration
     */
    public TacletIndex createTacletIndex() {
	return new TacletIndex(unit.getSetOfTaclet());
    }

    
}
