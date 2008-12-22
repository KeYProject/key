package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.visualization.*;

import java.util.*;

/**
 * Extracts the code, for which we want to create a unittest, from a formula of
 * the form: &lt updates&gt \\&lt code\\&gt post.
 */
public class TestCodeExtractor {

    // private Term modTerm;
    private Services serv;
    private ExecutionTraceModel tr;

    private Statement[] testCode = null;
    private Term post = null;
    private PackageReference context = null;
    private StatementBlock sb = null;

    // the name of the file the method under test is located in
    private String fileName = null;
    // the package of the containing class
    // private String packageName = null;
    // the method we want to test
    private String methodName = null;
    private static int testCounter = 0;
    private Namespace newPVs = new Namespace();
    private Namespace pvn;
    private NRFLHandler nrflHan;

    public TestCodeExtractor(ExecutionTraceModel tr, Services serv,
            Namespace pvn) {
        this.tr = tr;
        this.serv = serv;
        this.pvn = pvn;
    }

    // MAYBE OBSOLETE
    // public Statement[] extractTestCode(){
    // if(testCode != null){
    // return testCode;
    // }
    // Semisequent succ = getNodeForCodeExtraction(tr).sequent().succedent();
    // for(int i=0; i<succ.size(); i++){
    // Term current = new NRFLtoProgVar().transform(succ.get(i).formula());
    // ListOfStatement statements = SLListOfStatement.EMPTY_LIST;
    // //TODO: Resolve data dependencies in simultaneous updates.
    // while(current.op() instanceof IUpdateOperator){
    // statements = statements.append(getAssignments(current));
    // current = current.sub(current.op().arity()-1);
    // }
    // if(current.op() instanceof Modality){
    // post = current.sub(0);
    // sb = (StatementBlock) current.javaBlock().program();
    // collectUndeclaredVariables(sb);
    // statements = statements.append(flatten(sb));
    // testCode = statements.toArray();
    // return testCode;
    // }
    // }
    // throw new NotTranslatableException("Could not extract testcode");
    // }

    public Statement[] extractTestCode() {
        if (testCode != null) {
            return testCode;
        }
        final TraceElement trace = tr.getFirstTraceElement();
        nrflHan = new NRFLHandler(serv, this, trace.getPosOfModality());

        Term current = nrflHan.getResult();
        ListOfStatement statements = SLListOfStatement.EMPTY_LIST;
        // TODO: Resolve data dependencies in simultaneous updates.
        while (current.op() instanceof IUpdateOperator) {
            statements = statements.append(getAssignments(current));
            current = current.sub(current.op().arity() - 1);
        }
        if (current.op() instanceof Modality) {
            post = current.sub(0);
            sb = (StatementBlock) trace.getProgram();
            collectUndeclaredVariables(sb);
            statements = statements.append(flatten(sb));
            testCode = statements.toArray();
            return testCode;
        }
        throw new NotTranslatableException("Could not extract testcode");
    }

    /**
     * Collects variables not explicitely declared in the IUT.
     */
    private void collectUndeclaredVariables(StatementBlock sb) {
        JavaASTCollector coll = new JavaASTCollector(sb, ProgramVariable.class);
        coll.start();
        ListOfProgramElement l = coll.getNodes();
        IteratorOfProgramElement it = l.iterator();
        while (it.hasNext()) {
            ProgramVariable pv = (ProgramVariable) it.next();
            if (pvn.lookup(pv.name()) == pv) {
                newPVs.add(pv);
            }
        }
        coll = new JavaASTCollector(sb, LocalVariableDeclaration.class);
        coll.start();
        l = coll.getNodes();
        it = l.iterator();
        ListOfNamed lon = newPVs.allElements();
        while (it.hasNext()) {
            LocalVariableDeclaration lvd = (LocalVariableDeclaration) it.next();
            ArrayOfVariableSpecification vars = lvd.getVariables();
            for (int i = 0; i < vars.size(); i++) {
                IProgramVariable pv = vars.getVariableSpecification(i)
                        .getProgramVariable();
                if (pvn.lookup(pv.name()) == pv) {
                    lon = lon.removeAll(pv);
                }
            }
        }
        newPVs = new Namespace();
        while (!lon.isEmpty()) {
            newPVs.add(lon.head());
            lon = lon.tail();
        }
    }

    public HashSet<Statement> getStatements() {
        if (sb != null) {
            return getStatements(sb);
        }
        return new HashSet<Statement>();
    }

    private HashSet<Statement> getStatements(StatementBlock sbl) {
        HashSet<Statement> result = new HashSet<Statement>();
        for (int i = 0; i < sbl.getChildCount(); i++) {
            Statement s = sbl.getStatementAt(i);
            if (s instanceof StatementBlock) {
                result.addAll(getStatements((StatementBlock) s));
            } else if (s instanceof MethodBodyStatement) {
                JavaASTCollector coll = new JavaASTCollector(
                        ((MethodBodyStatement) s).getBody(serv),
                        Statement.class);
                coll.start();
                ListOfProgramElement l = coll.getNodes();
                IteratorOfProgramElement it = l.iterator();
                while (it.hasNext()) {
                    Statement next = (Statement) it.next();
                    if (!(next instanceof StatementContainer)) {
                        result.add(next);
                    }
                }
            } else {
                result.add(s);
            }
        }
        return result;
    }

    public Node getNodeForCodeExtraction(ExecutionTraceModel tr) {
        Node node = tr.getFirstTraceElement().node();
        while (!node.root()) {
            node = node.parent();
        }
        while (node.childrenCount() == 1
                && node != tr.getFirstTraceElement().node()) {
            node = node.child(0);
        }
        return node;
    }

    private ListOfStatement flatten(StatementBlock sb) {
        ListOfStatement result = SLListOfStatement.EMPTY_LIST;
        for (int i = 0; i < sb.getStatementCount(); i++) {
            if (fileName == null) {
                fileName = sb.getStatementAt(i).getPositionInfo().getFileName();
            }
            if (sb.getStatementAt(i) instanceof StatementBlock) {
                result = result.append(flatten((StatementBlock) sb
                        .getStatementAt(i)));
            } else if (sb.getStatementAt(i) instanceof MethodBodyStatement) {
                result = result
                        .append(convertMBSToMethodCall((MethodBodyStatement) sb
                                .getStatementAt(i)));
            } else {
                result = result.append(sb.getStatementAt(i));
            }
        }
        return result;
    }

    /**
     * Returns the formula from which an oracle for the extracted code can be
     * created.
     */
    public Term getTermForOracle() {
        if (post == null) {
            extractTestCode();
        }
        return post;
    }

    /**
     * Returns the package the code under test is located in.
     */
    public PackageReference getPackage() {
        if (context == null) {
            extractTestCode();
        }
        return context;
    }

    /**
     * Transforms updates into assignment expressions.
     */
    private ListOfStatement getAssignments(Term t) {
        ListOfStatement result = SLListOfStatement.EMPTY_LIST;
        IUpdateOperator uop = (IUpdateOperator) t.op();
        Term currLoc;
        for (int i = 0; i < uop.locationCount(); i++) {
            currLoc = uop.location(t, i);
            if (currLoc.op() instanceof NonRigidFunctionLocation) {
                result = result.append(nrflHan.getWriteRep(currLoc.op()));
            } else {
                Expression l, r;
                l = (Expression) convertToProgramElement(currLoc);
                r = (Expression) convertToProgramElement(uop.value(t, i));
                result = result.append(TestGenerator
                        .assignmentOrSet(l, r, serv));
            }
        }
        return result;
    }

    public Expression convertToProgramElement(Term t) {
        t = TestGenerator.replaceConstants(t, serv, newPVs);
        return serv.getTypeConverter().convertToProgramElement(t);
    }

    /**
     * Returns the program variables newly introduced as substitution for skolem
     * constants and those found in the IUT.
     */
    public SetOfProgramVariable getNewProgramVariables() {
        SetOfProgramVariable result = SetAsListOfProgramVariable.EMPTY_SET;
        IteratorOfNamed it = newPVs.allElements().iterator();
        while (it.hasNext()) {
            result = result.add((ProgramVariable) it.next());
        }
        return result;
    }

    private Statement convertMBSToMethodCall(MethodBodyStatement mbs) {
        methodName = mbs.getProgramMethod(serv).getMethodDeclaration()
                .getName();
        String sortName = mbs.getProgramMethod(serv).getContainerType()
                .getSort().name().toString();
        fileName = sortName.substring(sortName.lastIndexOf(".") + 1, sortName
                .length());
        // if(sortName.lastIndexOf(".")!=-1){
        // packageName = sortName.substring(0, sortName.lastIndexOf("."));
        // }
        MethodReference mr = new MethodReference(mbs.getArguments(),
                new ProgramElementName(mbs.getProgramMethod(serv).getName()),
                mbs.getProgramMethod(serv).isStatic() ? new TypeRef(mbs
                        .getProgramMethod(serv).getContainerType()) : mbs
                        .getDesignatedContext());
        context = mbs.getProgramMethod(serv).getContainerType()
                .createPackagePrefix();
        if (mbs.getResultVariable() != null) {
            ProgramVariable rv = (ProgramVariable) mbs.getResultVariable();
            newPVs.add(rv);
            return new CopyAssignment(rv, mr);
        } else {
            return mr;
        }
    }

    public String getFileName() {
        return (fileName == null ? "Generic" : fileName) + (testCounter++);
    }

    // public String getPackageName(){
    // return packageName;
    // }

    public String getMethodName() {
        return (methodName == null ? "code" : methodName);
    }

}
