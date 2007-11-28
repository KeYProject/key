// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.mgt;

import java.util.*;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofSaver;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.util.Debug;

/**
 * represents a contract on the DynamicLogic level, that is pre-condition,
 * program, post-condition, and modifies clause. It is the starting point to
 * create both proof obligation (to ensure that the contract is valid) as well
 * as a taclet (that allows to use the contract in a proof). DLMethodContracts
 * are created from UserKeYProblemFiles using the \contract section. Moreover
 * they are created when a contract of another input like JML or OCL is
 * configured.
 * @deprecated
 * 
 */
public class DLMethodContract extends DefaultOperationContract {

    private Term                    pre;
    private Term                    atPreAxioms;
    private Collection              atPreFunctions;
    private Modality                modality;
    private ModelMethod             modelMethod;
    private Statement               stmt;    
    private Term                    post;
    private SetOfLocationDescriptor modifies;    
    private NamespaceSet            namespaces;
    private String                  displayName;
    private String                  name;
    private Services                services;


    private static Statement extractStatement(Term fma) {
        JavaProgramElement pe = fma.javaBlock().program();
        return (Statement) ((NonTerminalProgramElement) pe).getChildAt(0);
    }

    static Statement unwrapBlocks(Statement s, boolean stopAtCatchAll) {
        while (s instanceof StatementBlock
                || (s instanceof CatchAllStatement && !stopAtCatchAll)
                || s instanceof Catch) {
            s = ((StatementContainer) s).getStatementAt(0);
        }
        return s;
    }

    /**
     * Creates a DLMethodContract with one implication formula of the form
     * <code>pre -> \<p\> post</code> and a modifies clause
     * 
     * @param fma
     *            the implication formula
     * @param modifies
     *            a set of location descriptors defining the modifies clause for
     *            this DLMethodContract
     * @param name
     *            a unique identifying name for a contract in the proof
     * @param displayName
     *            the name displayed for this contract
     * @param services
     *            the services object
     * @param namespaces
     *            the namespaces for looking up atpre functions
     */
    public DLMethodContract(Term fma, SetOfLocationDescriptor modifies,
            String name, String displayName, Services services,
            NamespaceSet namespaces) {

        this(fma.sub(0), fma.sub(1).sub(0), null, null, extractStatement(fma
                .sub(1)), modifies, (Modality) fma.sub(1).op(), name,
                displayName, services, namespaces.copy());

        setupAtPreFunctions(fma, namespaces);
    }

    /**
     * Creates a DLMethodContract with separate parts and possible additional
     * preconditions which are not to be proven in the precondition branch of
     * the created proof.
     * 
     * @param pre
     *            the precondition of the contract
     * @param post
     *            the postcondition of the contract
     * @param extraPre
     *            the additional preconditions
     * @param atPreFunctions
     *            a Collection with all functions used to model <tt>@pre</tt> for function symbols
     * @param mbs
     *            the statement of the proof, either this is a method body
     *            statement or a catch all statement
     * @param modifies
     *            a set of location descriptors defining the modifies clause for
     *            this DLMethodContract
     * @param name
     *            a unique identifying name for a contract in the proof
     * @param displayName
     *            the name displayed for this contract
     * @param services
     *            the services object
     * @param namespaces
     *            the namespaces for looking up atpre functions
     */
    public DLMethodContract(Term pre, Term post, Term extraPre,
            Collection atPreFunctions, Statement mbs,
            SetOfLocationDescriptor modifies, Modality modality, String name,
            String displayName, Services services, NamespaceSet namespaces) {

        assert pre != null && post != null;

        this.pre = pre;
        this.post = post;
        this.atPreAxioms = extraPre;
        this.atPreFunctions = atPreFunctions == null ? new HashSet()
                : atPreFunctions;
        this.stmt = mbs;
        this.modifies = modifies;
        this.modality = modality;
        this.name = name;
        this.displayName = displayName;
        this.services = services;
        this.namespaces = namespaces;
        this.modelMethod = new JavaModelMethod(getProgramMethod(), services
                .getJavaInfo().getJavaSourcePath(), services);
    }

    /**
     * @param namespaces
     * @param map
     */
    private void addAtPreFunctions(Namespace namespace, Map map) {
        if (namespace instanceof AtPreNamespace) {
            final Map atPreMapping = ((AtPreNamespace) namespace)
                    .getAtPreMapping();
            map.putAll(atPreMapping);
            atPreFunctions.addAll(atPreMapping.values());
        }
    }

    public void addPost(Term t) {
        post = TermBuilder.DF.and(t, post);
    }

    public void addPre(Term t) {
        pre = TermBuilder.DF.and(t, pre);
    }

    public boolean applicableForModality(Modality mod) {
        return getModality().equals(ModalityClass.getNormReprModality(mod));
    }

    private ProgramVariable clone(ProgramVariable pv, Services services) {       
        final ProgramElementName name = services.getVariableNamer()
                .getTemporaryNameProposal(pv.name().toString());
        return new LocationVariable(name, pv.getKeYJavaType());
    }

    private RigidFunction clone(RigidFunction rf) {
	String basename = rf.name().toString().replaceAll("@pre", "AtPre");
        final String name = VariableNameProposer.DEFAULT.getNameProposal(basename, services, null);
        return new RigidFunction(new Name(name), rf.sort(), rf.argSort());
    }

    public DLMethodContract copy() {
        return new DLMethodContract(pre, post, atPreAxioms,
                getAtPreFunctions(), stmt, modifies, modality, name,
                displayName, services, namespaces);
    }

    public DLMethodContract createDLMethodContract(Proof proof) {
        final DLMethodContract c = copy();
        c.displayName = c.displayName + " (derived)";
        return c;
    }

    private Term createImplication() {
        final TermBuilder tb = TermBuilder.DF;
        final Term modalityTerm = tb.tf().createProgramTerm(modality,
                JavaBlock.createJavaBlock(new StatementBlock(getStatement())),
                getPost());
        return tb.imp(tb.and(getAdditionalAxioms(), getPre()), modalityTerm);
    }

    public String createProgramVarsSection() {
        final IteratorOfNamed it = namespaces.programVariables().allElements()
                .iterator();
        String result = "\n\n\\programVariables {\n";
        while (it.hasNext()) {
            ProgramVariable pv = (ProgramVariable) it.next();
            final Type javaType = pv.getKeYJavaType().getJavaType();

            final String typeName = javaType instanceof ArrayType ? ((ArrayType) javaType)
                    .getAlternativeNameRepresentation()
                    : javaType.getFullName();

            result += "    " + typeName + " " + pv.name() + ";\n";
        }
        result += "}\n";
        return result;
    }

    public boolean equals(Object cmp) {
        if (!(cmp instanceof OldOperationContract)) {
            return false;
        }
        if (!(cmp instanceof DLMethodContract)) {
            return cmp.equals(this);
        }
        DLMethodContract cmpHoare = (DLMethodContract) cmp;
        // TODO: This does not work if functions for @pre are introduced
        boolean b = cmpHoare.modelMethod.equals(modelMethod)
                && cmpHoare.atPreAxioms.equalsModRenaming(atPreAxioms)
                && cmpHoare.post.equalsModRenaming(post)
                && cmpHoare.pre.equalsModRenaming(pre)
                && cmpHoare.modality.equals(modality);
        if (!b || cmpHoare.modifies.size() != modifies.size())
            return false;
        return modifies.equals(cmpHoare.modifies);
    }

    protected Term getAdditionalAxioms() {
        return atPreAxioms;
    }

    private Collection getAtPreFunctions() {
        return atPreFunctions;
    }

    public CatchAllStatement getCatchAllStatement() {
        Statement s = unwrapBlocks(getStatement(), true);
        return (s instanceof CatchAllStatement) ? (CatchAllStatement) s : null;
    }

    public String getHTMLText() {
        return "<html>pre: "
                + getPreText()
                + "<br>post: "
                + getPostText()
                + "<br>modifies: "
                + getModifiesText()
                + "<br>termination: "
                + (getModality() == Op.DIA ? "total" : getModality().toString())
                + "</html>";
    }

    public MethodBodyStatement getMethodBodyStatement() {
        return (MethodBodyStatement) unwrapBlocks(getStatement(), false);
    }

    public Modality getModality() {
        return ModalityClass.getNormReprModality(modality);
    }

    public ModelMethod getModelMethod() {
        return modelMethod;
    }

    public SetOfLocationDescriptor getModifies() {
        return modifies;
    }

    public String getModifiesText() {
        return LogicPrinter.quickPrintLocationDescriptors(getModifies(), services);
    }

    public String getName() {
        return name;
    }

    /**
     * returns the object on which this contract is, in this case it is the
     * program statement of the contract; or in case that this is a method body
     * statement the according program method is returned.
     */
    public Object getObjectOfContract() {
        return getProgramMethod();
    }

    public Term getPost() {
        return post;
    }

    public String getPostText() {
        return ProofSaver.printTerm(getPost(), services).toString();
    }

    public Term getPre() {
        return pre;
    }

    public String getPreText() {
        return ProofSaver.printTerm(getPre(), services).toString();
    }

    public ProgramMethod getProgramMethod() {
        Object o = unwrapBlocks(getStatement(), false);
        if (o instanceof MethodBodyStatement) {
            return ((MethodBodyStatement) o).getProgramMethod(services);
        }
        Debug.fail();
        return null;
    }

    /**
     * returns a proof obligation input needed to show the corretcness of this
     * contract.
     * 
     */
    public ProofOblInput getProofOblInput(Proof proof) {
        return new DLHoareTriplePO(createImplication(), getModality(), header,
                getName(), services, this);
    }

    public Statement getStatement() {
        return stmt;
    }

    public int hashCode() {
        int result = 0;
        result = 37 * result + modelMethod.hashCode();
        result = 37 * result + modality.hashCode();
        result = 37 * result + atPreAxioms.hashCode();
        result = 37 * result + post.hashCode();
        result = 37 * result + pre.hashCode();
        result = 37 * result + modifies.hashCode();
        return result;
    }

    /**
     * @param replacementMap
     * @param localFunctions
     * @param localProgramVariables
     */
    protected void instantiateAtPreSymbols(Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables) {
        final Iterator it = getAtPreFunctions().iterator();
        while (it.hasNext()) {
            final RigidFunction rf = (RigidFunction) it.next();
            final RigidFunction newRf = clone(rf);
            localFunctions.addSafely(newRf);
            replacementMap.put(rf, newRf);
        }
    }

    protected void instantiateAuxiliarySymbols(Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables, Services services) {
        instantiateDLContractPV(replacementMap, localProgramVariables);
    }

    private void instantiateDLContractPV(Map replacementMap,
            Namespace programVariables) {
        final IteratorOfNamed it = namespaces.programVariables().elements()
                .iterator();
        while (it.hasNext()) {
            final ProgramVariable pv = (ProgramVariable) it.next();
            assert !pv.isMember();
            if (!replacementMap.containsKey(pv)) {
                final ProgramVariable newPV = clone(pv, services);
                programVariables.addSafely(newPV);
                replacementMap.put(pv, newPV);
            }
        }
    }

    /**
     * @param insts
     * @param replacementMap
     * @param localProgramVariables
     * @param localFunctions
     */
    protected void instantiateMethodParameters(
            MethodContractInstantiation insts, final Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables) {
        for (int i = 0, methodParameterSize = insts.getArgumentCount(); i < methodParameterSize; i++) {
            replacementMap.put(getMethodBodyStatement().getArguments()
                    .getExpression(i), insts.getArgumentAt(i));
        }
    }

    /**
     * @param insts
     * @param replacementMap
     * @param localProgramVariables
     * @param localFunctions
     */
    protected void instantiateMethodReceiver(MethodContractInstantiation insts,
            final Map replacementMap, Namespace localFunctions,
            Namespace localProgramVariables) {
        if (!getMethodBodyStatement().isStatic(services)) {
            // this can be a field reference for instance
            Term rec = services.getTypeConverter().convertToLogicElement(
                            insts.getReceiver());
            Sort recSort = rec.sort();
	    MethodBodyStatement mbs = null;
	    if(stmt instanceof CatchAllStatement) {
	      mbs = (MethodBodyStatement)((StatementBlock)((CatchAllStatement)stmt).getBody()).getBody().getStatement(0);
	    }else{
	      mbs = (MethodBodyStatement)stmt;
	    }
	    Sort actSort = mbs.getBodySource().getSort();
            if(!recSort.equals(actSort)) {
	      rec = TermFactory.DEFAULT.createFunctionTerm(((AbstractSort)actSort).getCastSymbol(), rec);
	    }
            replacementMap.put(getMethodBodyStatement().getDesignatedContext(),
                    rec);
        }
    }

    /**
     * @param insts
     * @param replacementMap
     * @param localProgramVariables
     * @param localFunctions
     */
    protected void instantiateMethodReturnVariable(
            MethodContractInstantiation insts, final Map replacementMap,
            Namespace localFunctions, Namespace localProgramVariables) {
        replacementMap.put(getMethodBodyStatement().getResultVariable(), insts
                .getResult());
    }

    public void setHeader(String s) {
        if (s == null)
            return;
        // 1. Check if there is a \programVariables section (I can
        // imagine an unlikely situation where it's actually missing),
        // if so, replace it with a "fresh" one
        int start = s.indexOf("\\programVariables");
        int end = -1;
        if (start != -1) {
            end = s.indexOf("}", start);
            header = s.substring(0, start) + createProgramVarsSection()
                    + s.substring(end + 1);
        } else {
            // 2. No? Then put it somewhere "on top"
            start = s.indexOf("\\withOptions");
            if (start != -1) {
                // Put it after \withOptions
                start = s.indexOf(";", start) + 1;
            } else {
                // Put it after \javaSource
                start = s.indexOf("\\javaSource");
                if (start != -1) {
                    start = s.indexOf(";", start) + 1;
                } else {
                    Debug
                            .fail("Your .key file is missing vital sections as far as this situation is concerned.");
                }
            }
            header = s.substring(0, start) + createProgramVarsSection()
                    + s.substring(start + 1);
        }
    }
    
    public String getHeader() {
      return header;
    }

    private void setupAtPreFunctions(Term fma, NamespaceSet namespaces) {
        final TermBuilder tb = TermBuilder.DF;
	final Map map = new TreeMap(new NameComparator()); 
        atPreFunctions = new HashSet();

        addAtPreFunctions(namespaces.programVariables(), map);
        addAtPreFunctions(namespaces.functions(), map);

        Term conj = tb.tt();

        final Iterator it = map.entrySet().iterator();

        while (it.hasNext()) {
            Map.Entry e = (Map.Entry) it.next();
            TermSymbol atPost = (TermSymbol) e.getKey();
            Function atPre = (Function) e.getValue();
            LogicVariable[] vars = new LogicVariable[atPost.arity()];

            if (atPost instanceof ProgramVariable
                    && ((ProgramVariable) atPost).isMember()
                    && !((ProgramVariable) atPost).isStatic()) {
                vars = new LogicVariable[] { new LogicVariable(new Name("x"),
                        atPre.argSort(0)) };
            } else {
                for (int i = 0; i < vars.length; i++) {
                    vars[i] = new LogicVariable(new Name("x" + i),
                            ((Function) atPost).argSort(i));
                }
            }

            final Term[] varTerms = new Term[vars.length];
            for (int i = 0; i < vars.length; i++) {
                varTerms[i] = tb.var(vars[i]);
            }

            final Term atPostTerm;
            if ((atPost instanceof ProgramVariable)
                    && ((ProgramVariable) atPost).isMember()
                    && !((ProgramVariable) atPost).isStatic()) {
                atPostTerm = tb.dot(varTerms[0], (ProgramVariable) atPost);
            } else {
                atPostTerm = tb.func(atPost, varTerms);
            }

            final Term atPreTerm = tb.func(atPre, varTerms);
            conj = tb.and(conj, tb.all(vars, tb.equals(atPreTerm, atPostTerm)));
        }

        atPreAxioms = conj;

    }

    public Namespace getProgramVariables() {
        return namespaces.programVariables();
    }
    
    public String toString() {
        return "[DL Hoare Triple Contract] " + getName();
    }

    private class NameComparator implements Comparator {
       public int compare(Object o1, Object o2) {
         return ((Named)o1).name().compareTo(((Named)o2).name());
       }
    }

}
