package de.uka.ilkd.key.proof;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.visualdebugger.VisualDebuggerState;


/**
 * The node info object contains additional information about a node used to
 * give user feedback. The content does not have any influence on the proof or
 * carry something of logical value.
 */
public class NodeInfo {

    /** firstStatement stripped of method frames */
    private SourceElement activeStatement                 = null;

    private String        branchLabel                     = null;

    /** flag true if the first and active statement have been determined */
    private boolean       determinedFstAndActiveStatement = false;

    /** used for proof tree annotation when applicable */
    private SourceElement firstStatement                  = null;

    private String        firstStatementString            = null;

    /** the node this info object belongs to */
    private final Node    node;

    /** has the rule app of the node been applied interactively? */
    private boolean interactiveApplication = false;    
     
    // ALL fields below are for the eclipse symbolic debugger plug-in
    // THEY HAVE TO BE MOVED OUT TO THE DEBUGGER package
    // where a separate mapping node <-> debugger status has to be maintained
    private final VisualDebuggerState visualDebuggerState = new VisualDebuggerState();
   
    
    public NodeInfo(Node node) {
        this.node = node;
    }


    private static List symbolicExecNames = new ArrayList(5);
    static {
        symbolicExecNames.add(new Name("simplify_prog"));
        symbolicExecNames.add(new Name("simplify_autoname"));
        symbolicExecNames.add(new Name("executeIntegerAssignment"));
        symbolicExecNames.add(new Name("simplify_object_creation"));
    }


    /**
     * determines the first and active statement if the applied
     * taclet worked on a modality     
     */
    private void determineFirstAndActiveStatement() {
        if (determinedFstAndActiveStatement)
            return;
        final RuleApp ruleApp = node.getAppliedRuleApp();
        if (ruleApp instanceof PosTacletApp) {
            PosTacletApp pta = (PosTacletApp) ruleApp;
            if (!isSymbolicExecution(pta.taclet())) return;
            Term t = pta.posInOccurrence().subTerm();
            final ProgramElement pe = t.executableJavaBlock().program();
            if (pe != null) {
                firstStatement = pe.getFirstElement();
                firstStatementString = null;

                activeStatement = firstStatement;
                while ((activeStatement instanceof ProgramPrefix)
                        && !(activeStatement instanceof StatementBlock)) {
                    activeStatement = activeStatement.getFirstElement();
                }
            }
            determinedFstAndActiveStatement = true;
        }
    }
    
    private boolean isSymbolicExecution(Taclet t) {
        ListOfRuleSet list = t.getRuleSets();
	RuleSet       rs;
	while (!list.isEmpty()) {
	    rs = list.head ();
            Name name = rs.name();
	    if (symbolicExecNames.contains(name)) return true;
	    list = list.tail();
	}
	return false;
    }

    /** 
     * returns the active statement of the JavaBlock the applied
     * rule has been matched against or null if no rule has been applied yet
     * or the applied rule was no taclet or program transformation rule
     */
    public SourceElement getActiveStatement() {
	determineFirstAndActiveStatement();
        return activeStatement;
    }

    /**
     * returns the branch label
     */
    public String getBranchLabel() {
        return branchLabel;
    }

    /**
     * returns the name of the source file where the active statement
     * occurs or the string <tt>NONE</tt> if the statement does not originate from a 
     * source file (e.g. created by a taclet application or part of a 
     * generated implicit method)    
     */
    public String getExecStatementParentClass() {
        determineFirstAndActiveStatement();
        if (activeStatement instanceof JavaSourceElement)
            return ((JavaSourceElement) activeStatement).getPositionInfo()
                    .getFileName();
        return "<NONE>";
    }

    /**
     * returns the position of the executed statement in its source code 
     * or Position.UNDEFINED 
     */
    public Position getExecStatementPosition() {
        determineFirstAndActiveStatement();
        return (activeStatement == null) ? Position.UNDEFINED : activeStatement
                .getStartPosition();
    }

    /**
     * returns a string representation of the first statement or null if no such
     * exists
     */
    public String getFirstStatementString() {
        determineFirstAndActiveStatement();
        if (firstStatement != null) {
            if (firstStatementString == null) {
                firstStatementString = "" + firstStatement;
            }
            firstStatementString = "" + activeStatement;
            return firstStatementString;
        }
        return null;
    }

    /**
     * sets the branch label of a node. Schema variables occuring
     * in string <tt>s</tt> are replaced by their instantiations if
     * possible
     * @param s the String to be set
     */
    public void setBranchLabel(String s) {
        determineFirstAndActiveStatement();
        if (s == null)
            return;
        RuleApp ruleApp = node.parent().getAppliedRuleApp();
        if (ruleApp instanceof TacletApp) { 
            TacletApp tacletApp = (TacletApp) ruleApp; // XXX

            Pattern p = Pattern.compile("#\\w+");
            Matcher m = p.matcher(s);
            StringBuffer sb = new StringBuffer();
            while (m.find()) {
                String arg = m.group();
                Object val = tacletApp.instantiations().lookupValue(new Name(arg));
                if (val == null) {
                    // chop off the leading '#'
                    String arg2 = arg.substring(1, arg.length());
                    val = tacletApp.instantiations().lookupValue(new Name(arg2));
                }
                String res;
                if (val == null) {
                    System.err.println("No instantiation for " + arg
                            + ". Probably branch label not up to date in "
                            + tacletApp.rule().name());
                    res = arg; // use sv name instead
                } else
                    res = ProofSaver.printAnything(val, node.proof().getServices());
                m.appendReplacement(sb, res);
            }
            m.appendTail(sb);
            branchLabel = sb.toString();
        } else {
            branchLabel = s; 
        }
    }

    /**
     * parameter indicated if the rule has been applied interactively or
     * not
     * @param b a boolean indicating interactive application 
     */
    public void setInteractiveRuleApplication(boolean b) {
        interactiveApplication = b;
    }
    
    /**
     * returns true if the rule applied on this node has been performed
     * manually by the user
     */
    public boolean getInteractiveRuleApplication() {
        return interactiveApplication;
    }
   
    /**
     * returns the visual debugger state
     * @return the visual debugger state
     */
    public VisualDebuggerState getVisualDebuggerState() {
        return visualDebuggerState;
    }

}
