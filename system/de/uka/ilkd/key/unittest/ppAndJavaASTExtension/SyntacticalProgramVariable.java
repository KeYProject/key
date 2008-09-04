package de.uka.ilkd.key.unittest.ppAndJavaASTExtension;

import java.io.IOException;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceData;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.ReferenceSuffix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramInLogic;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;

/**
 * This class in analogously implemented to class 
 * {@link de.uka.ilkd.key.logic.op.ProgramVariable}
 * but it does not support {@code KeYJavaType}s but only {@code Type}s. Its purpose
 * is only for syntactical representation in the java AST in order to be printable
 * by the {@link CompilableJavaPP}. The objective of its independence from 
 * {@code KeYJavaType}s to prevent objects of this class to escape in other parts 
 * of the system like, e.g. {@code JavaInfo}. See Bug #911.
 * @author gladisch
 */
public class SyntacticalProgramVariable extends TermSymbol implements
        SourceElement, ProgramElement, Expression, ReferencePrefix,
        IProgramVariable, ParsableVariable, ReferenceSuffix, ProgramInLogic {

    // attention: this counter is used to get a unique variable name, once the
    // names are unique the counter should be removed %%%%
    private static long COUNTER = 0;

    private long id;

    /**In contrast to ProgramVariable this field is not of type KeYJavaType but only a type Type */
    public final Type type;

    private final boolean isStatic;

    private final boolean isModel;

    private final boolean isGhost;

    private final boolean isFinal;

    
    /** represents the type where this program variable is declared if and only if
    the program variable denotes a field.
    In contrast to ProgramVariable this field is not of type KeYJavaType but only a type Type.*/
    private final Type containingType;

    protected SyntacticalProgramVariable(ProgramElementName name, Sort s,
            Type t, Type containingType, boolean isStatic,
            boolean isModel, boolean isGhost, boolean isFinal) {
        super(name, s);
        this.type = t;
        this.containingType = containingType;
        this.isStatic = isStatic;
        this.isModel = isModel;
        this.isGhost = isGhost;
        this.isFinal = isFinal;
        // remove this as soon as possible %%%
        id = COUNTER;
        COUNTER++;
    }

    protected SyntacticalProgramVariable(ProgramElementName name, Sort s,
            Type t, Type containingType, boolean isStatic,
            boolean isModel, boolean isGhost) {
        this(name, s, t, containingType, isStatic, isModel, isGhost, false);
    }
//chris von locationvariable
    public SyntacticalProgramVariable(ProgramElementName name, Type t) {
        this(name, null, t, null, false, false, false);
        //this(name, new Sort(t.name..), t, null, false, false, false);
    }
    
    /** returns unique id %%%% HACK */
    public long id() {
        return id;
    }

    /** returns sort */
    public Sort sort() {
        //return super.sort() == null ? type.getSort() : super.sort(); chris
        return super.sort();
    }

    /** @return arity of the Variable as int */
    public int arity() {
        return 0;
    }

    /** @return name of the SyntacticalProgramVariable */
    public ProgramElementName getProgramElementName() {
        return (ProgramElementName) name();
    }

    /** toString */
    public String toString() {
        return name().toString();
    }

    /**
     * returns true if the program variable has been declared as static
     */
    public boolean isStatic() {
        return isStatic;
    }

    public boolean isModel() {
        return isModel;
    }

    /**
     * returns true if the program variable has been declared as ghost
     */
    public boolean isGhost() {
        return isGhost;
    }

    /**
     * returns true if the program variable has been declared as final
     */
    public boolean isFinal() {
        return isFinal;
    }

    /**
     * returns true if the program variable is a member
     */
    public boolean isMember() {
        return containingType != null;
    }

    /**
     * returns the KeYJavaType where the program variable is declared or null if
     * the program variable denotes not a field
     */
    public Type getContainerType() {
        return containingType;
    }

    public SourceElement getFirstElement() {
        return this;
    }

    public SourceElement getLastElement() {
        return this;
    }

    public Comment[] getComments() {
        return new Comment[0];
    }

    /**
     * calls the corresponding method of a visitor in order to perform some
     * action/transformation on this element
     * 
     * @param v
     *            the Visitor
     */
    public void visit(de.uka.ilkd.key.java.visitor.Visitor v) {
        v.performActionOnIProgramVariable(this);
    }

    /** @param w must be an instance of CompilableJavaPP */
    public void prettyPrint(PrettyPrinter w) throws IOException {
        CompilableJavaPP cjpp = (CompilableJavaPP)w;
        cjpp.printSyntacticalProgramVariable(this);
    }

    /**
     * Returns the start position of the primary token of this element. To get
     * the start position of the syntactical first token, call the corresponding
     * method of <CODE>getFirstElement()</CODE>.
     * 
     * @return the start position of the primary token.
     */
    public Position getStartPosition() {
        return Position.UNDEFINED;
    }

    /**
     * Returns the end position of the primary token of this element. To get the
     * end position of the syntactical first token, call the corresponding
     * method of <CODE>getLastElement()</CODE>.
     * 
     * @return the end position of the primary token.
     */
    public Position getEndPosition() {
        return Position.UNDEFINED;
    }

    /**
     * Returns the relative position (number of blank heading lines and columns)
     * of the primary token of this element. To get the relative position of the
     * syntactical first token, call the corresponding method of
     * <CODE>getFirstElement()</CODE>.
     * 
     * @return the relative position of the primary token.
     */
    public Position getRelativePosition() {
        return Position.UNDEFINED;
    }

    public PositionInfo getPositionInfo() {
        return PositionInfo.UNDEFINED;
    }

    /**If you *effectively* want to call getKeYJavaType().getJavaType() then 
     * just use the {@code type} attribute of this class instead.
     * This method should never be called because SyntacticalProgramVariable is supposed
     * to be independent from KeYJavaTypes. This method is declared to overwritte
     * the respective method from the parent class.
     */
    public KeYJavaType getKeYJavaType() {
        throw new RuntimeException("SyntactialProgramVariable.getKeYJavaType should never be called.\n" +
                        " If you *effectively* want to call getKeYJavaType().getJavaType() then\n" +
                        " just use the type attribute of this class instead.");
        //return null;
    }

    public KeYJavaType getKeYJavaType(Services javaServ) {
        return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getKeYJavaType();
    }

    /**
     * We do not have a prefix, so fake it! This way we implement
     * ReferencePrefix
     * 
     * @author VK
     */
    public ReferencePrefix getReferencePrefix() {
        return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
        return this;
    }

    /**
     * equals modulo renaming is described in the corresponding comment in class
     * SourceElement. In this case two SyntacticalProgramVariables are
     * considered to be equal if they are assigned to the same abstract name or
     * if they are the same object.
     */
    public boolean equalsModRenaming(SourceElement se, NameAbstractionTable nat) {
        return nat.sameAbstractName(this, se);
    }

    public Expression convertToProgram(Term t, ExtList l) {
        if (isStatic()) {
            ExtList l2 = new ExtList();
            l2.add(this);
            return new FieldReference(l2, new SyntacticalTypeRef(
                    getContainerType()));
        } else {
            return this;
        }
    }

    public String proofToString() {
        final Type javaType = type;//chris .getJavaType()
        final String typeName;
        if (javaType instanceof ArrayType) {
            typeName = ((ArrayType) javaType)
                    .getAlternativeNameRepresentation();
        } else {
            typeName = javaType.getFullName();
        }
        return typeName + " " + name() + ";\n";
    }

    public boolean isImplicit() {
        return getProgramElementName().getProgramName().startsWith("<");
    }

    /*
     * (non-Javadoc)
     * 
     * @see
     * de.uka.ilkd.key.logic.op.Location#mayBeAliasedBy(de.uka.ilkd.key.logic
     * .op.Location)
     */
    public boolean mayBeAliasedBy(Location loc) {
        return loc instanceof SortedSchemaVariable || loc == this;
    }

    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        source.next();
        if (src == this) {
            return matchCond;
        } else {
            Debug
                    .out(
                            "Program match failed. Not same program variable (pattern, source)",
                            this, src);
            return null;
        }
    }
}
