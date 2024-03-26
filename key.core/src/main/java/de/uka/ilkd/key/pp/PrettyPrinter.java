/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.pp;

import java.util.Objects;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;

import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * A configurable pretty printer for Java source elements originally from COMPOST.
 *
 * @author AL
 *
 *         CHANGED FOR KeY. Comments are not printed!
 */
@NullMarked
public class PrettyPrinter implements Visitor {
    private static final Logger LOGGER = LoggerFactory.getLogger(PrettyPrinter.class);

    private final PosTableLayouter layouter;

    private boolean startAlreadyMarked;
    @Nullable
    private Object firstStatement;
    private boolean endAlreadyMarked;

    private final SVInstantiations instantiations;
    @Nullable
    private final Services services;
    private boolean usePrettyPrinting;
    private boolean useUnicodeSymbols;

    /** creates a new PrettyPrinter */
    public PrettyPrinter(PosTableLayouter out) {
        this(out, SVInstantiations.EMPTY_SVINSTANTIATIONS, null, true, true);
    }

    public PrettyPrinter(PosTableLayouter o, SVInstantiations svi, @Nullable Services services,
            boolean usePrettyPrinting, boolean useUnicodeSymbols) {
        this.layouter = o;
        this.instantiations = svi;
        this.services = services;
        this.usePrettyPrinting = usePrettyPrinting;
        this.useUnicodeSymbols = useUnicodeSymbols;
    }

    /**
     * Creates a PrettyPrinter that does not create a position table.
     */
    public static PrettyPrinter purePrinter() {
        return new PrettyPrinter(PosTableLayouter.pure());
    }

    public static String getTypeNameForAccessMethods(String typeName) {
        typeName = typeName.replace('[', '_');
        return typeName.replace('.', '_');
    }

    /**
     * @return the result
     */
    public String result() {
        return layouter.result();
    }

    /**
     * Entry method for this class.
     * Be careful when using other method directly since they might need an enclosing block.
     *
     * @param e what to print
     */
    public void print(SourceElement e) {
        layouter.beginRelativeC(0);
        performActionOnStatement(e);
        layouter.end();
    }

    /**
     * Alternative entry method for this class. Omits the trailing semicolon in the output.
     *
     * @param s source element to print
     */
    public void printFragment(SourceElement s) {
        layouter.beginRelativeC(0);
        markStart(s);
        s.visit(this);
        markEnd(s);
        layouter.end();
    }

    /**
     * Marks the start of the first executable statement ...
     *
     * @param stmt current statement;
     */
    protected void markStart(Object stmt) {
        if (!startAlreadyMarked) {
            layouter.markStartFirstStatement();
            firstStatement = stmt;
            startAlreadyMarked = true;
        }
    }

    /**
     * Marks the end of the first executable statement ...
     */
    protected void markEnd(Object stmt) {
        if (!endAlreadyMarked && (firstStatement == stmt)) {
            layouter.markEndFirstStatement();
            endAlreadyMarked = true;
        }
    }

    /**
     * Replace all unicode characters above ? by their explicit representation.
     *
     * @param str the input string.
     * @return the encoded string.
     */
    protected static String encodeUnicodeChars(String str) {
        int len = str.length();
        StringBuilder buf = new StringBuilder(len + 4);
        for (int i = 0; i < len; i += 1) {
            char c = str.charAt(i);
            if (c >= 0x0100) {
                if (c < 0x1000) {
                    buf.append("\\u0").append(Integer.toString(c, 16));
                } else {
                    buf.append("\\u").append(Integer.toString(c, 16));
                }
            } else {
                buf.append(c);
            }
        }
        return buf.toString();
    }

    /**
     * Write keyword list.
     *
     * @param list a program element list.
     */
    protected void writeKeywordList(ImmutableArray<Modifier> list) {
        for (int i = 0; i < list.size(); i++) {
            if (i != 0) {
                layouter.brk();
            }
            performActionOnModifier(list.get(i));
        }
    }

    /**
     * Write comma list.
     *
     * @param list a program element list.
     */
    protected void writeCommaList(ImmutableArray<? extends ProgramElement> list) {
        for (int i = 0; i < list.size(); i++) {
            if (i != 0) {
                layouter.print(",").brk();
            }
            list.get(i).visit(this);
        }
    }

    protected void printOperator(Operator x, String symbol) {
        ImmutableArray<Expression> children = x.getArguments();
        if (children != null) {
            layouter.beginC();
            switch (x.getArity()) {
            case 2 -> {
                children.get(0).visit(this);
                layouter.print(" ");
                layouter.print(symbol);
                layouter.brk();
                children.get(1).visit(this);
            }
            case 1 -> {
                switch (x.getNotation()) {
                case Operator.PREFIX -> {
                    layouter.print(symbol);
                    children.get(0).visit(this);
                }
                case Operator.POSTFIX -> {
                    children.get(0).visit(this);
                    layouter.print(symbol);
                }
                default -> {
                }
                }
            }
            }
            layouter.end();
        }
    }

    private void beginMultilineBracket() {
        layouter.print("(").beginRelativeC(0).beginRelativeC().brk(0);
    }

    private void endMultilineBracket() {
        layouter.end().brk(0).end();
        layouter.print(")");
    }

    private void printReferencePrefix(ReferencePrefix p) {
        if (p != null) {
            p.visit(this);
            layouter.print(".");
        }
    }

    private void printArguments(ImmutableArray<? extends Expression> args) {
        beginMultilineBracket();
        if (args != null) {
            writeCommaList(args);
        }
        endMultilineBracket();
    }

    @Override
    public void performActionOnProgramElementName(ProgramElementName x) {
        String name = x.getProgramName();
        boolean isKey = (name.equals("int") || name.equals("float") || name.equals("char")
                || name.equals("short") || name.equals("long") || name.equals("boolean"));
        if (isKey) {
            layouter.keyWord(name);
        } else {
            layouter.print(name);
        }
    }

    @Override
    public void performActionOnProgramVariable(ProgramVariable x) {
        layouter.print(x.name().toString());
    }

    @Override
    public void performActionOnProgramMethod(IProgramMethod x) {
        layouter.print(x.getMethodDeclaration().getProgramElementName().toString());
    }

    @Override
    public void performActionOnProgramMetaConstruct(ProgramTransformer x) {
        layouter.print(x.name().toString());
        layouter.print("(");
        if (x.getChildAt(0) != null) {
            x.getChildAt(0).visit(this);
        }
        layouter.print(")");
    }

    @Override
    public void performActionOnContextStatementBlock(ContextStatementBlock x) {
        if (x.getStatementCount() > 0) {
            layouter.beginRelativeC();
            layouter.print("{ ..");
            for (Statement statement : x.getBody()) {
                layouter.nl();
                performActionOnStatement(statement);
            }
            layouter.end().nl();
            layouter.print("... }");
        } else {
            layouter.print("{ ..  ... }");
        }
    }

    @Override
    public void performActionOnIntLiteral(IntLiteral x) {
        layouter.print(x.getValueString());
    }

    @Override
    public void performActionOnBooleanLiteral(BooleanLiteral x) {
        layouter.keyWord(x.getValue() ? "true" : "false");
    }

    @Override
    public void performActionOnEmptySetLiteral(EmptySetLiteral x) {
        layouter.keyWord("\\empty");
    }

    private void printDLFunctionOperator(String name, Operator operator) {
        layouter.keyWord(name);
        if (operator.getArity() > 0) {
            printArguments(operator.getArguments());
        }
    }

    @Override
    public void performActionOnSingleton(de.uka.ilkd.key.java.expression.operator.adt.Singleton x) {
        printDLFunctionOperator("\\singleton", x);
    }

    @Override
    public void performActionOnSetUnion(de.uka.ilkd.key.java.expression.operator.adt.SetUnion x) {
        printDLFunctionOperator("\\set_union", x);
    }

    @Override
    public void performActionOnIntersect(Intersect x) {
        printDLFunctionOperator("\\intersect", x);
    }

    @Override
    public void performActionOnSetMinus(de.uka.ilkd.key.java.expression.operator.adt.SetMinus x) {
        printDLFunctionOperator("\\set_minus", x);
    }


    @Override
    public void performActionOnAllFields(de.uka.ilkd.key.java.expression.operator.adt.AllFields x) {
        printDLFunctionOperator("\\all_fields", x);
    }

    @Override
    public void performActionOnAllObjects(
            de.uka.ilkd.key.java.expression.operator.adt.AllObjects x) {
        printDLFunctionOperator("\\all_objects", x);
    }

    @Override
    public void performActionOnEmptySeqLiteral(EmptySeqLiteral x) {
        layouter.print("\\seq_empty");
    }

    @Override
    public void performActionOnSeqLength(SeqLength x) {
        x.getChildAt(0).visit(this);
        layouter.print(".length");
    }

    @Override
    public void performActionOnSeqGet(SeqGet x) {
        x.getChildAt(0).visit(this);
        layouter.print("[");
        x.getChildAt(1).visit(this);
        layouter.print("]");
    }

    @Override
    public void performActionOnSeqSingleton(
            de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton x) {
        printDLFunctionOperator("\\seq_singleton", x);
    }

    @Override
    public void performActionOnSeqConcat(de.uka.ilkd.key.java.expression.operator.adt.SeqConcat x) {
        printDLFunctionOperator("\\singleton", x);
    }

    @Override
    public void performActionOnSeqIndexOf(
            de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf x) {
        printDLFunctionOperator("\\indexOf", x);
    }

    @Override
    public void performActionOnSeqSub(de.uka.ilkd.key.java.expression.operator.adt.SeqSub x) {
        printDLFunctionOperator("\\seq_sub", x);
    }

    @Override
    public void performActionOnSeqReverse(
            de.uka.ilkd.key.java.expression.operator.adt.SeqReverse x) {
        printDLFunctionOperator("\\seq_reverse", x);
    }

    @Override
    public void performActionOnSeqPut(
            de.uka.ilkd.key.java.expression.operator.adt.SeqPut x) {
        printDLFunctionOperator("\\seq_upd", x);
    }

    @Override
    public void performActionOnDLEmbeddedExpression(DLEmbeddedExpression x) {
        layouter.print("\\dl_" + x.getFunctionSymbol().name());
        layouter.print("(");

        for (int i = 0; i < x.getChildCount(); i++) {
            if (i != 0) {
                layouter.print(",").brk();
            }
            x.getChildAt(i).visit(this);
        }
        layouter.print(")");
    }

    @Override
    public void performActionOnStringLiteral(StringLiteral x) {
        layouter.print(encodeUnicodeChars(x.getValue()));
    }

    @Override
    public void performActionOnNullLiteral(NullLiteral x) {
        layouter.keyWord("null");
    }

    @Override
    public void performActionOnCharLiteral(CharLiteral x) {
        layouter.print(encodeUnicodeChars(x.toString()));
    }

    @Override
    public void performActionOnDoubleLiteral(DoubleLiteral x) {
        layouter.print(x.getValue());
    }

    @Override
    public void performActionOnMergePointStatement(MergePointStatement x) {
        layouter.beginC().print("//@ merge_point (").brk(0);
        x.getExpression().visit(this);
        layouter.brk(0).print(");");
    }

    @Override
    public void performActionOnLongLiteral(LongLiteral x) {
        layouter.print(x.getValueString());
    }

    @Override
    public void performActionOnFloatLiteral(FloatLiteral x) {
        layouter.print(x.getValue());
    }

    @Override
    public void performActionOnPackageSpecification(PackageSpecification x) {
        layouter.nl();
        layouter.keyWord("package");
        layouter.print(" ");
        performActionOnPackageReference(x.getPackageReference());
        layouter.print(";");
    }

    @Override
    public void performActionOnAssert(Assert x) {
        layouter.keyWord("assert");
        layouter.print(" ");

        x.getCondition().visit(this);

        if (x.getMessage() != null) {
            layouter.print(" :");
            layouter.brk();
            x.getMessage().visit(this);
        }
    }

    @Override
    public void performActionOnProgramConstant(ProgramConstant constant) {
        performActionOnProgramVariable(constant);
    }

    @Override
    public void performActionOnAbstractProgramElement(AbstractProgramElement x) {
        if (!(x instanceof SchemaTypeReference)) {
            throw new UnsupportedOperationException();
        }
        performActionOnSchemaTypeReference((SchemaTypeReference) x);
    }

    @Override
    public void performActionOnIProgramVariable(IProgramVariable x) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x) {
        // No idea what to do here
    }

    @Override
    public void performActionOnParameterDeclaration(ParameterDeclaration x) {
        performActionOnVariableDeclaration(x);
    }

    @Override
    public void performActionOnFieldSpecification(FieldSpecification x) {
        performActionOnVariableSpecification(x);
    }

    @Override
    public void performActionOnImplicitFieldSpecification(ImplicitFieldSpecification x) {
        performActionOnVariableSpecification(x);
    }

    @Override
    public void performActionOnSchematicFieldReference(SchematicFieldReference x) {
        performActionOnFieldReference(x);
    }

    @Override
    public void performActionOnVariableReference(VariableReference x) {
        performActionOnProgramVariable(x.getProgramVariable());
    }

    @Override
    public void performActionOnConstructorDeclaration(ConstructorDeclaration x) {
        performActionOnMethodDeclaration(x);
    }

    @Override
    public void performActionOnForUpdates(ForUpdates x) {
        writeCommaList(x.getUpdates());
    }

    @Override
    public void performActionOnGuard(Guard x) {
        var child = x.getChildAt(0);
        if (child != null) {
            child.visit(this);
        }
    }

    @Override
    public void performActionOnLoopInit(LoopInit x) {
        writeCommaList(x.getInits());
    }

    @Override
    public void performActionOnLocationVariable(LocationVariable variable) {
        performActionOnProgramVariable(variable);
    }

    @Override
    public void performActionOnLoopInvariant(LoopSpecification x) {
        layouter.print("//@ loop-invariant");
    }

    @Override
    public void performActionOnBlockContract(BlockContract x) {
        layouter.print("//@ block-contract");
    }

    @Override
    public void performActionOnLoopContract(LoopContract x) {
        layouter.print("//@ loop-contract");
    }

    @Override
    public void performActionOnBlockContract(StatementBlock oldBlock, StatementBlock newBlock) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void performActionOnLoopContract(StatementBlock oldBlock, StatementBlock newBlock) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void performActionOnLoopContract(LoopStatement oldLoop, LoopStatement newLoop) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void performActionOnMergeContract(MergeContract x) {
        layouter.print("//@ merge-contract");
    }

    @Override
    public void performActionOnArrayDeclaration(ArrayDeclaration type) {
        Type baseType = type.getBaseType().getKeYJavaType().getJavaType();
        assert baseType != null;
        if (baseType instanceof ArrayDeclaration) {
            performActionOnArrayDeclaration((ArrayDeclaration) baseType);
        } else {
            layouter.print(baseType.getFullName());
        }
        layouter.print("[]");
    }

    @Override
    public void performActionOnTypeReference(TypeReference x) {
        performActionOnTypeReference(x, false);
    }

    public void performActionOnTypeReference(TypeReference x, boolean fullTypeNames) {
        if (x.getKeYJavaType() != null
                && x.getKeYJavaType().getJavaType() instanceof ArrayDeclaration) {
            performActionOnArrayDeclaration((ArrayDeclaration) x.getKeYJavaType().getJavaType());
        } else if (x.getProgramElementName() != null) {
            printTypeReference(x.getReferencePrefix(), x.getKeYJavaType(),
                x.getProgramElementName(), fullTypeNames);
        }
    }

    private void printTypeReference(ReferencePrefix prefix, KeYJavaType type,
            ProgramElementName name, boolean fullTypeNames) {
        printReferencePrefix(prefix);
        if (fullTypeNames) {
            layouter.print(type.getFullName());
        } else {
            performActionOnProgramElementName(name);
        }
    }

    public void performActionOnSchemaTypeReference(SchemaTypeReference x) {
        performActionOnTypeReference(x, false);
    }

    @Override
    public void performActionOnFieldReference(FieldReference x) {
        if (x.getName() != null
                && "javax.realtime.MemoryArea::currentMemoryArea".equals(x.getName())) {
            layouter.print("<currentMemoryArea>");
        } else {
            printTypeReference(x.getReferencePrefix(), x.getKeYJavaType(),
                x.getProgramElementName(), false);
        }
    }

    @Override
    public void performActionOnPackageReference(PackageReference x) {
        printTypeReference(x.getReferencePrefix(), null, x.getProgramElementName(), false);
    }

    @Override
    public void performActionOnThrows(Throws x) {
        if (x.getExceptions() != null) {
            layouter.keyWord("throws").print(" ");
            writeCommaList(x.getExceptions());
        }
    }

    @Override
    public void performActionOnArrayInitializer(ArrayInitializer x) {
        layouter.print("{");
        if (x.getArguments() != null) {
            writeCommaList(x.getArguments());
        }
        layouter.print("}");
    }

    @Override
    public void performActionOnCompilationUnit(CompilationUnit x) {
        boolean hasPackageSpec = x.getPackageSpecification() != null;
        if (hasPackageSpec) {
            performActionOnPackageSpecification(x.getPackageSpecification());
        }
        boolean hasImports = (x.getImports() != null) && (!x.getImports().isEmpty());
        if (hasImports) {
            if (hasPackageSpec) {
                layouter.nl();
            }
            for (Import i : x.getImports()) {
                layouter.nl();
                performActionOnImport(i);
            }
        }
        if (x.getDeclarations() != null) {
            if (hasImports || hasPackageSpec) {
                layouter.nl();
            }
            for (TypeDeclaration td : x.getDeclarations()) {
                layouter.nl();
                td.visit(this);
            }
        }
    }

    @Override
    public void performActionOnClassDeclaration(ClassDeclaration x) {
        layouter.beginC();
        ImmutableArray<Modifier> mods = x.getModifiers();
        boolean hasMods = mods != null && !mods.isEmpty();
        if (hasMods) {
            writeKeywordList(mods);
        }
        if (x.getProgramElementName() != null) {
            if (hasMods) {
                layouter.print(" ");
            }
            layouter.keyWord("class").print(" ");
            performActionOnProgramElementName(x.getProgramElementName());
        }
        if (x.getExtendedTypes() != null) {
            layouter.print(" ");
            performActionOnExtends(x.getExtendedTypes());
        }
        if (x.getImplementedTypes() != null) {
            layouter.print(" ");
            performActionOnImplements(x.getImplementedTypes());
        }
        // not an anonymous class
        if (x.getProgramElementName() != null) {
            layouter.print(" ");
        }
        if (x.getMembers() != null) {
            beginBlock();
            for (MemberDeclaration m : x.getMembers()) {
                layouter.nl();
                m.visit(this);
            }
            endBlock();
        } else {
            layouter.print("{}");
        }
    }

    @Override
    public void performActionOnInterfaceDeclaration(InterfaceDeclaration x) {
        layouter.beginC();
        ImmutableArray<Modifier> mods = x.getModifiers();
        boolean hasMods = mods != null && !mods.isEmpty();
        if (hasMods) {
            writeKeywordList(mods);
        }
        if (x.getProgramElementName() != null) {
            if (hasMods) {
                layouter.print(" ");
            }
            layouter.keyWord("interface").print(" ");
            performActionOnProgramElementName(x.getProgramElementName());
        }
        if (x.getExtendedTypes() != null) {
            layouter.print(" ");
            performActionOnExtends(x.getExtendedTypes());
        }
        layouter.print(" ");

        if (x.getMembers() != null) {
            beginBlock();
            for (MemberDeclaration m : x.getMembers()) {
                layouter.nl();
                m.visit(this);
            }
            endBlock();
        } else {
            layouter.print("{}");
        }
    }

    @Override
    public void performActionOnFieldDeclaration(FieldDeclaration x) {
        performActionOnVariableDeclaration(x);
    }

    @Override
    public void performActionOnLocalVariableDeclaration(LocalVariableDeclaration x) {
        performActionOnVariableDeclaration(x);
    }

    @Override
    public void performActionOnVariableDeclaration(VariableDeclaration x) {
        layouter.beginI();
        ImmutableArray<Modifier> modifiers = x.getModifiers();
        if (modifiers != null && !modifiers.isEmpty()) {
            writeKeywordList(modifiers);
            layouter.print(" ");
        }
        x.getTypeReference().visit(this);
        layouter.print(" ");
        ImmutableArray<? extends VariableSpecification> varSpecs = x.getVariables();
        if (varSpecs != null) {
            writeCommaList(varSpecs);
        }
        layouter.end();
    }

    @Override
    public void performActionOnMethodDeclaration(MethodDeclaration x) {
        layouter.beginC();
        ImmutableArray<Modifier> mods = x.getModifiers();
        boolean hasMods = mods != null && !mods.isEmpty();
        if (hasMods) {
            writeKeywordList(mods);
            layouter.print(" ");
        }
        if (x.getTypeReference() != null) {
            x.getTypeReference().visit(this);
            layouter.print(" ");
        } else if (x.getTypeReference() == null && !(x instanceof ConstructorDeclaration)) {
            layouter.keyWord("void");
            layouter.print(" ");
        }
        performActionOnProgramElementName(x.getProgramElementName());
        layouter.print(" ");

        beginMultilineBracket();
        if (x.getParameters() != null) {
            writeCommaList(x.getParameters());
        }
        endMultilineBracket();
        if (x.getThrown() != null) {
            performActionOnThrows(x.getThrown());
        }
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        } else {
            layouter.print(";");
        }
    }

    @Override
    public void performActionOnClassInitializer(ClassInitializer x) {
        layouter.beginC();
        if (x.getModifiers() != null) {
            writeKeywordList(x.getModifiers());
            layouter.print(" ");
        }
        layouter.end();
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    protected void performActionOnStatement(SourceElement s) {
        layouter.beginRelativeC(0);
        boolean validStatement = !(s instanceof CatchAllStatement || s instanceof ProgramPrefix);
        if (validStatement) {
            markStart(s);
        }
        s.visit(this);
        if (validStatement) {
            markEnd(s);
        }
        if (!(s instanceof BranchStatement) && !(s instanceof StatementContainer)) {
            layouter.print(";");
        }
        layouter.end();
    }

    @Override
    public void performActionOnStatementBlock(StatementBlock x) {
        printStatementBlock(x);
    }

    private void beginBlock() {
        layouter.print("{");
        layouter.beginRelativeC();
    }

    private void endBlock() {
        layouter.end().nl().print("}");
    }

    public boolean printStatementBlock(StatementBlock x) {
        boolean emptyBlock = x.getBody() == null || x.getBody().isEmpty();
        if (emptyBlock) {
            // We have an empty statement block ...
            markStart(x);
            layouter.print("{}");
            markEnd(x);
            return false;
        } else {
            beginBlock();
            for (Statement statement : x.getBody()) {
                layouter.nl();
                performActionOnStatement(statement);
            }
            endBlock();
            return true;
        }
    }

    @Override
    public void performActionOnBreak(Break x) {
        layouter.keyWord("break");
        if (x.getProgramElementName() != null) {
            layouter.brk();
            x.getProgramElementName().visit(this);
        }
    }

    @Override
    public void performActionOnContinue(Continue x) {
        layouter.keyWord("continue");
        if (x.getProgramElementName() != null) {
            layouter.brk();
            x.getProgramElementName().visit(this);
        }
    }

    @Override
    public void performActionOnReturn(Return x) {
        layouter.keyWord("return");
        if (x.getExpression() != null) {
            layouter.brk();
            x.getExpression().visit(this);
        }
    }

    @Override
    public void performActionOnThrow(Throw x) {
        layouter.keyWord("throw");
        if (x.getExpression() != null) {
            layouter.brk();
            x.getExpression().visit(this);
        }
    }

    @Override
    public void performActionOnDo(Do x) {
        performActionOnDo(x, true);
    }

    private boolean handleBlockOrSingleStatement(Statement body) {
        if (body instanceof StatementBlock) {
            layouter.print(" ");
            return printStatementBlock((StatementBlock) body);
        } else {
            layouter.beginRelativeC();
            layouter.brk();
            body.visit(this);
            if (!(body instanceof BranchStatement) && !(body instanceof StatementContainer)) {
                layouter.print(";");
            }
            layouter.end();
            return false;
        }
    }

    private boolean handleBlockStatementOrEmpty(Statement body, boolean includeBody) {
        if (includeBody) {
            if (body == null || body instanceof EmptyStatement) {
                layouter.print(";");
                return false;
            } else {
                return handleBlockOrSingleStatement(body);
            }
        } else {
            layouter.print(" ... ");
            return false;
        }
    }

    public void performActionOnDo(Do x, boolean includeBody) {
        layouter.keyWord("do");

        boolean newBlock = handleBlockStatementOrEmpty(x.getBody(), includeBody);
        handleContinuationAfterNewBlock(newBlock);

        layouter.keyWord("while");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.getGuard() != null) {
            x.getGuard().visit(this);
        }
        endMultilineBracket();
        layouter.print(";");
    }

    @Override
    public void performActionOnEnhancedFor(EnhancedFor x) {
        performActionOnEnhancedFor(x, true);
    }

    public void performActionOnEnhancedFor(EnhancedFor x, boolean includeBody) {
        layouter.keyWord("for");
        layouter.print(" ");
        beginMultilineBracket();

        ImmutableArray<LoopInitializer> initializers = x.getInitializers();
        if (initializers != null) {
            initializers.get(0).visit(this);
        }

        layouter.print(" :");
        layouter.brk();

        if (x.getGuard() != null) {
            x.getGuardExpression().visit(this);
        }

        endMultilineBracket();

        handleBlockStatementOrEmpty(x.getBody(), includeBody);
    }

    @Override
    public void performActionOnFor(For x) {
        performActionOnFor(x, true);
    }

    public void performActionOnFor(For x, boolean includeBody) {
        layouter.keyWord("for");
        layouter.print(" ");
        beginMultilineBracket();

        // there is no "getLoopInit" method
        // so get the first child of the for loop

        ILoopInit init = x.getILoopInit();
        if (init != null) {
            init.visit(this);
        }
        layouter.print(";").brk();
        if (x.getGuardExpression() != null) {
            x.getGuardExpression().visit(this);
        }
        layouter.print(";").brk();

        IForUpdates upd = x.getIForUpdates();
        if (upd != null) {
            upd.visit(this);
        }
        endMultilineBracket();

        handleBlockStatementOrEmpty(x.getBody(), includeBody);
    }

    @Override
    public void performActionOnWhile(While x) {
        performActionOnWhile(x, true);
    }

    public void performActionOnWhile(While x, boolean includeBody) {
        layouter.keyWord("while");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.getGuardExpression() != null) {
            x.getGuardExpression().visit(this);
        }
        endMultilineBracket();

        handleBlockStatementOrEmpty(x.getBody(), includeBody);
    }

    @Override
    public void performActionOnIf(If x) {
        performActionOnIf(x, true);
    }

    private void handleContinuationAfterNewBlock(boolean newBlock) {
        if (newBlock) {
            layouter.print(" ");
        } else {
            layouter.nl();
        }
    }

    public void performActionOnIf(If x, boolean includeBranches) {
        layouter.keyWord("if");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.getExpression() != null) {
            x.getExpression().visit(this);
        }
        endMultilineBracket();

        if (includeBranches) {
            boolean newBlock = handleBlockOrSingleStatement(x.getThen().getBody());
            if (x.getElse() != null) {
                handleContinuationAfterNewBlock(newBlock);
            }
            Else e = x.getElse();
            if (x.getElse() != null) {
                performActionOnElse(e);
            }
        }
    }

    @Override
    public void performActionOnSwitch(Switch x) {
        performActionOnSwitch(x, true);
    }

    public void performActionOnSwitch(Switch x, boolean includeBranches) {
        layouter.keyWord("switch");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.getExpression() != null) {
            x.getExpression().visit(this);
        }
        endMultilineBracket();

        if (includeBranches) {
            layouter.print(" ");
            beginBlock();
            for (Branch branch : x.getBranchList()) {
                layouter.nl();
                branch.visit(this);
            }
            endBlock();
        }
    }

    private void printTryLike(String name, StatementBlock body, ImmutableArray<Branch> branches) {
        layouter.keyWord(name);
        layouter.print(" ");
        if (body != null) {
            printStatementBlock(body);
        }
        if (branches != null) {
            for (Branch branch : branches) {
                branch.visit(this);
            }
        }
    }

    @Override
    public void performActionOnTry(Try x) {
        printTryLike("try", x.getBody(), x.getBranchList());
    }

    @Override
    public void performActionOnLabeledStatement(LabeledStatement x) {
        if (x.getLabel() != null) {
            x.getLabel().visit(this);
            layouter.print(":");
        }

        if (x.getBody() != null) {
            layouter.nl();
            performActionOnStatement(x.getBody());
        }
    }

    @Override
    public void performActionOnMethodFrame(MethodFrame x) {
        layouter.keyWord("method-frame");
        layouter.print(" ");
        beginMultilineBracket();

        IProgramVariable var = x.getProgramVariable();
        var exec = x.getExecutionContext();
        if (var != null) {
            layouter.beginRelativeC().print("result->");
            var.visit(this);
            if (exec != null) {
                layouter.print(",");
            }
            layouter.end();
            if (exec != null) {
                layouter.brk();
            }
        }

        if (exec instanceof ExecutionContext) {
            performActionOnExecutionContext((ExecutionContext) exec);
        } else if (exec != null) {
            performActionOnSchemaVariable((SchemaVariable) exec);
        }

        endMultilineBracket();
        layouter.print(" ");

        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnCatchAllStatement(CatchAllStatement x) {
        layouter.keyWord("#catchAll").print(" ");
        beginMultilineBracket();
        performActionOnLocationVariable(x.getParam());
        endMultilineBracket();
        x.getBody().visit(this);
    }

    @Override
    public void performActionOnMethodBodyStatement(MethodBodyStatement x) {
        IProgramVariable pvar = x.getResultVariable();
        if (pvar != null) {
            pvar.visit(this);
            layouter.brk(1, 0);
            layouter.print("=");
            layouter.brk(1, 0);
        }

        printMethodReference(x.getMethodReference());
        // CHG:
        layouter.print("@");
        final TypeReference tr = x.getBodySourceAsTypeReference();
        if (tr instanceof SchemaTypeReference) {
            performActionOnSchemaTypeReference((SchemaTypeReference) tr);
        } else if (tr instanceof SchemaVariable) {
            performActionOnSchemaVariable((SchemaVariable) tr);
        } else {
            tr.visit(this);
        }
    }

    @Override
    public void performActionOnSynchronizedBlock(SynchronizedBlock x) {
        layouter.print("synchronized");
        if (x.getExpression() != null) {
            beginMultilineBracket();
            x.getExpression().visit(this);
            endMultilineBracket();
        }
        if (x.getBody() != null) {
            layouter.print(" ");
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnLoopScopeBlock(LoopScopeBlock x) {
        layouter.keyWord("loop-scope");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.getIndexPV() != null) {
            x.getIndexPV().visit(this);
        }
        endMultilineBracket();
        layouter.print(" ");
        printStatementBlock(x.getBody());
    }

    @Override
    public void performActionOnImport(Import x) {
        layouter.print("import ");
        x.getReference().visit(this);
        if (x.isMultiImport()) {
            layouter.print(".*;");
        } else {
            layouter.print(";");
        }
    }

    @Override
    public void performActionOnExtends(Extends x) {
        if (x.getSupertypes() != null) {
            layouter.keyWord("extends").print(" ");
            writeCommaList(x.getSupertypes());
        }
    }

    @Override
    public void performActionOnImplements(Implements x) {
        if (x.getSupertypes() != null) {
            layouter.keyWord("implements").print(" ");
            writeCommaList(x.getSupertypes());
        }
    }

    @Override
    public void performActionOnVariableSpecification(VariableSpecification x) {
        x.getProgramVariable().visit(this);
        for (int i = 0; i < x.getDimensions(); i += 1) {
            layouter.print("[]");
        }
        if (x.getInitializer() != null) {
            layouter.print(" = ");
            x.getInitializer().visit(this);
        }
    }

    @Override
    public void performActionOnBinaryAnd(BinaryAnd x) {
        printOperator(x, "&");
    }

    @Override
    public void performActionOnBinaryAndAssignment(BinaryAndAssignment x) {
        printOperator(x, "&=");
    }

    @Override
    public void performActionOnBinaryOrAssignment(BinaryOrAssignment x) {
        printOperator(x, "|=");
    }

    @Override
    public void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x) {
        printOperator(x, "^=");
    }

    @Override
    public void performActionOnCopyAssignment(CopyAssignment x) {
        x.getArguments().get(0).visit(this);
        layouter.print(" = ");
        x.getArguments().get(1).visit(this);
    }

    @Override
    public void performActionOnDivideAssignment(DivideAssignment x) {
        printOperator(x, "/=");
    }

    @Override
    public void performActionOnMinusAssignment(MinusAssignment x) {
        printOperator(x, "-=");
    }

    @Override
    public void performActionOnModuloAssignment(ModuloAssignment x) {
        printOperator(x, "%=");
    }

    @Override
    public void performActionOnPlusAssignment(PlusAssignment x) {
        printOperator(x, "+=");
    }

    @Override
    public void performActionOnPostDecrement(PostDecrement x) {
        printOperator(x, "--");
    }

    @Override
    public void performActionOnPostIncrement(PostIncrement x) {
        printOperator(x, "++");
    }

    @Override
    public void performActionOnPreDecrement(PreDecrement x) {
        printOperator(x, "--");
    }

    @Override
    public void performActionOnPreIncrement(PreIncrement x) {
        printOperator(x, "++");
    }

    @Override
    public void performActionOnShiftLeftAssignment(ShiftLeftAssignment x) {
        printOperator(x, "<<=");
    }

    @Override
    public void performActionOnShiftRightAssignment(ShiftRightAssignment x) {
        printOperator(x, ">>=");
    }

    @Override
    public void performActionOnTimesAssignment(TimesAssignment x) {
        printOperator(x, "*=");
    }

    @Override
    public void performActionOnUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x) {
        printOperator(x, ">>>=");
    }

    @Override
    public void performActionOnBinaryNot(BinaryNot x) {
        printOperator(x, "~");
    }

    @Override
    public void performActionOnBinaryOr(BinaryOr x) {
        printOperator(x, "|");
    }

    @Override
    public void performActionOnBinaryXOr(BinaryXOr x) {
        printOperator(x, "^");
    }

    @Override
    public void performActionOnConditional(Conditional x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (x.getArguments() != null) {
            layouter.beginC();
            if (addParentheses) {
                layouter.print("(");
            }
            x.getArguments().get(0).visit(this);
            layouter.print(" ?").brk();
            x.getArguments().get(1).visit(this);
            layouter.print(" :").brk();
            x.getArguments().get(2).visit(this);
            if (addParentheses) {
                layouter.print(")");
            }
            layouter.end();
        }
    }

    @Override
    public void performActionOnDivide(Divide x) {
        printOperator(x, "/");
    }

    @Override
    public void performActionOnEquals(Equals x) {
        printOperator(x, "==");
    }

    @Override
    public void performActionOnGreaterOrEquals(GreaterOrEquals x) {
        printOperator(x, ">=");
    }

    @Override
    public void performActionOnGreaterThan(GreaterThan x) {
        printOperator(x, ">");
    }

    @Override
    public void performActionOnLessOrEquals(LessOrEquals x) {
        printOperator(x, "<=");
    }

    @Override
    public void performActionOnLessThan(LessThan x) {
        printOperator(x, "<");
    }

    @Override
    public void performActionOnNotEquals(NotEquals x) {
        printOperator(x, "!=");
    }

    @Override
    public void performActionOnNewArray(NewArray x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            layouter.print("(");
        }
        layouter.print("new ");

        x.getTypeReference().visit(this);
        int i = 0;
        if (x.getArguments() != null) {
            for (; i < x.getArguments().size(); i += 1) {
                layouter.print("[");
                x.getArguments().get(i).visit(this);
                layouter.print("]");
            }
        }
        for (; i < x.getDimensions(); i += 1) {
            layouter.print("[]");
        }
        if (x.getArrayInitializer() != null) {
            performActionOnArrayInitializer(x.getArrayInitializer());
        }
        if (addParentheses) {
            layouter.print(")");
        }
    }

    private void printInstanceOfLike(TypeOperator op, String kw) {
        boolean addParentheses = op.isToBeParenthesized();
        if (addParentheses) {
            layouter.print("(");
        }
        if (op.getArguments() != null) {
            op.getExpressionAt(0).visit(this);
        }
        layouter.print(" ");
        layouter.keyWord(kw);
        layouter.brk();
        if (op.getTypeReference() != null) {
            op.getTypeReference().visit(this);
        }
        if (addParentheses) {
            layouter.print(")");
        }
    }

    @Override
    public void performActionOnInstanceof(Instanceof x) {
        printInstanceOfLike(x, "instanceof");
    }


    @Override
    public void performActionOnExactInstanceof(ExactInstanceof x) {
        printInstanceOfLike(x, "exactInstanceof");
    }

    @Override
    public void performActionOnNew(New x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            layouter.print("(");
        }
        printReferencePrefix(x.getReferencePrefix());
        layouter.keyWord("new").print(" ");

        x.getTypeReference().visit(this);
        printArguments(x.getArguments());
        if (x.getClassDeclaration() != null) {
            performActionOnClassDeclaration(x.getClassDeclaration());
        }
        if (addParentheses) {
            layouter.print(")");
        }
    }

    @Override
    public void performActionOnTypeCast(TypeCast x) {
        boolean addParentheses = x.isToBeParenthesized();
        if (addParentheses) {
            layouter.print("(");
        }
        layouter.print("(");
        if (x.getTypeReference() != null) {
            x.getTypeReference().visit(this);
        }
        layouter.print(") ");
        if (x.getArguments() != null) {
            x.getArguments().get(0).visit(this);
        }
        if (addParentheses) {
            layouter.print(")");
        }
    }

    @Override
    public void performActionOnLogicalAnd(LogicalAnd x) {
        printOperator(x, "&&");
    }

    @Override
    public void performActionOnLogicalNot(LogicalNot x) {
        printOperator(x, "!");
    }

    @Override
    public void performActionOnLogicalOr(LogicalOr x) {
        printOperator(x, "||");
    }

    @Override
    public void performActionOnMinus(Minus x) {
        printOperator(x, "-");
    }

    @Override
    public void performActionOnModulo(Modulo x) {
        printOperator(x, "%");
    }

    @Override
    public void performActionOnNegative(Negative x) {
        printOperator(x, "-");
    }

    @Override
    public void performActionOnPlus(Plus x) {
        printOperator(x, "+");
    }

    @Override
    public void performActionOnPositive(Positive x) {
        printOperator(x, "+");
    }

    @Override
    public void performActionOnShiftLeft(ShiftLeft x) {
        printOperator(x, "<<");
    }

    @Override
    public void performActionOnShiftRight(ShiftRight x) {
        printOperator(x, ">>");
    }

    @Override
    public void performActionOnTimes(Times x) {
        printOperator(x, "*");
    }

    @Override
    public void performActionOnUnsignedShiftRight(UnsignedShiftRight x) {
        printOperator(x, ">>>");
    }

    @Override
    public void performActionOnArrayReference(ArrayReference x) {
        x.getReferencePrefix().visit(this);
        int s = x.getDimensionExpressions().size();
        for (int i = 0; i < s; i += 1) {
            layouter.print("[");
            x.getDimensionExpressions().get(i).visit(this);
            layouter.print("]");
        }
    }

    @Override
    public void performActionOnMetaClassReference(MetaClassReference x) {
        if (x.getTypeReference() != null) {
            x.getTypeReference().visit(this);
            layouter.print(".");
        }
        layouter.print("class");
    }

    @Override
    public void performActionOnMethodReference(MethodReference x) {
        printMethodReference(x);
    }

    protected void printMethodReference(MethodReference x) {
        printReferencePrefix(x.getReferencePrefix());
        if (x.getProgramElementName() != null) {
            x.getMethodName().visit(this);
        }

        printArguments(x.getArguments());
    }

    @Override
    public void performActionOnMethod(IProgramMethod x) {
        layouter.print(x.name().toString());
    }

    public void writeFullMethodSignature(IProgramMethod x) {
        layouter.print(x.getName());
        layouter.print("(");
        boolean afterFirst = false;
        for (ParameterDeclaration pd : x.getParameters()) {
            if (afterFirst) {
                layouter.print(", ");
            } else {
                afterFirst = true;
            }
            performActionOnTypeReference(pd.getTypeReference(), true);
        }
        layouter.print(")");
    }

    @Override
    public void performActionOnExecutionContext(ExecutionContext x) {
        layouter.beginRelativeC();
        layouter.print("source=");
        writeFullMethodSignature(x.getMethodContext());
        layouter.print("@");
        x.getTypeReference().visit(this);
        if (x.getRuntimeInstance() != null) {
            layouter.print(",").end().brk().beginRelativeC().print("this=");
            x.getRuntimeInstance().visit(this);
            layouter.end();
        } else {
            layouter.end();
        }
    }

    @Override
    public void performActionOnSuperConstructorReference(SuperConstructorReference x) {
        printReferencePrefix(x.getReferencePrefix());
        layouter.keyWord("super");
        printArguments(x.getArguments());
    }

    @Override
    public void performActionOnThisConstructorReference(ThisConstructorReference x) {
        layouter.keyWord("this");
        printArguments(x.getArguments());
    }

    @Override
    public void performActionOnSuperReference(SuperReference x) {
        printReferencePrefix(x.getReferencePrefix());
        layouter.keyWord("super");
    }

    @Override
    public void performActionOnThisReference(ThisReference x) {
        printReferencePrefix(x.getReferencePrefix());
        layouter.keyWord("this");
    }

    @Override
    public void performActionOnArrayLengthReference(ArrayLengthReference x) {
        printReferencePrefix(x.getReferencePrefix());
        layouter.print("length");
    }

    @Override
    public void performActionOnThen(Then x) {
        handleBlockOrSingleStatement(x.getBody());
    }

    @Override
    public void performActionOnElse(Else x) {
        layouter.keyWord("else");
        Statement body = x.getBody();
        if (body instanceof If) {
            layouter.print(" ");
            performActionOnIf((If) body);
        } else {
            handleBlockOrSingleStatement(body);
        }
    }

    private void printCaseBody(ImmutableArray<Statement> body) {
        if (body != null && !body.isEmpty()) {
            for (int i = 0; i < body.size(); i++) {
                Statement statement = body.get(i);
                if (statement instanceof StatementBlock) {
                    if (i != 0) {
                        layouter.nl();
                    } else {
                        layouter.print(" ");
                    }
                    printStatementBlock((StatementBlock) statement);
                } else {
                    layouter.nl();
                    layouter.beginRelativeC();
                    performActionOnStatement(statement);
                    layouter.end();
                }
            }
        }
    }

    @Override
    public void performActionOnCase(Case x) {
        layouter.beginRelativeC();
        layouter.keyWord("case").brk();
        if (x.getExpression() != null) {
            x.getExpression().visit(this);
        }
        layouter.print(":").end();
        printCaseBody(x.getBody());
    }

    @Override
    public void performActionOnCatch(Catch x) {
        layouter.print(" ");
        layouter.keyWord("catch");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.getParameterDeclaration() != null) {
            performActionOnParameterDeclaration(x.getParameterDeclaration());
        }
        endMultilineBracket();
        layouter.print(" ");
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnDefault(Default x) {
        layouter.keyWord("default").print(":");
        printCaseBody(x.getBody());
    }

    @Override
    public void performActionOnFinally(Finally x) {
        layouter.print(" ");
        layouter.keyWord("finally");
        layouter.print(" ");
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnModifier(Modifier x) {
        layouter.keyWord(x.getText());
    }

    @SuppressWarnings("unchecked")
    @Override
    public void performActionOnSchemaVariable(SchemaVariable x) {
        if (!(x instanceof ProgramSV)) {
            throw new UnsupportedOperationException(
                "Don't know how to pretty print non program SV in programs.");
        }

        Object o = instantiations.getInstantiation(x);
        if (o == null) {
            layouter.print(x.name().toString());
        } else {
            if (o instanceof ProgramElement) {
                ((ProgramElement) o).visit(this);
            } else if (o instanceof ImmutableArray) {
                for (ProgramElement e : ((ImmutableArray<ProgramElement>) o)) {
                    e.visit(this);
                }
            } else {
                LOGGER.warn("No PrettyPrinting available for {}", o.getClass().getName());
            }
        }
    }

    @Override
    public void performActionOnEmptyStatement(EmptyStatement x) {}

    @Override
    public void performActionOnComment(Comment x) {
        // l.print("/* " + x.getText().trim() + " */");
    }

    @Override
    public void performActionOnParenthesizedExpression(ParenthesizedExpression x) {
        layouter.print("(");
        if (x.getArguments() != null) {
            x.getArguments().get(0).visit(this);
        }
        layouter.print(")");
    }

    @Override
    public void performActionOnPassiveExpression(PassiveExpression x) {
        layouter.print("@(");
        if (x.getArguments() != null) {
            x.getArguments().get(0).visit(this);
        }
        layouter.print(")");
    }

    @Override
    public void performActionOnTransactionStatement(TransactionStatement x) {
        layouter.print(x.toString());
    }

    @Override
    public void performActionOnEmptyMapLiteral(EmptyMapLiteral x) {
        layouter.print("\\map_empty");
    }

    @Override
    public void performActionOnExec(Exec x) {
        printTryLike("exec", x.getBody(), x.getBranchList());
    }

    @Override
    public void performActionOnCcatch(Ccatch x) {
        layouter.print(" ");
        layouter.keyWord("ccatch");
        layouter.print(" ");
        beginMultilineBracket();
        if (x.hasParameterDeclaration()) {
            performActionOnParameterDeclaration(x.getParameterDeclaration());
        } else if (x.hasNonStdParameterDeclaration()) {
            x.getNonStdParameterDeclaration().visit(this);
        }
        endMultilineBracket();
        layouter.print(" ");
        if (x.getBody() != null) {
            printStatementBlock(x.getBody());
        }
    }

    @Override
    public void performActionOnCcatchReturnParameterDeclaration(
            CcatchReturnParameterDeclaration x) {
        layouter.keyWord("\\Return");
    }

    @Override
    public void performActionOnCcatchReturnValParameterDeclaration(
            CcatchReturnValParameterDeclaration x) {
        layouter.keyWord("\\Return");
        layouter.print(" ");
        x.getDelegate().visit(this);
    }

    @Override
    public void performActionOnCcatchContinueParameterDeclaration(
            CcatchContinueParameterDeclaration x) {
        layouter.keyWord("\\Continue");
    }

    @Override
    public void performActionOnCcatchBreakParameterDeclaration(CcatchBreakParameterDeclaration x) {
        layouter.keyWord("\\Break");
    }

    @Override
    public void performActionOnCcatchBreakLabelParameterDeclaration(
            CcatchBreakLabelParameterDeclaration x) {
        layouter.keyWord("\\Break");
        layouter.print(" ");
        if (x.getLabel() != null) {
            x.getLabel().visit(this);
        }
    }

    @Override
    public void performActionOnCCcatchContinueLabelParameterDeclaration(
            CcatchContinueLabelParameterDeclaration x) {
        layouter.keyWord("\\Continue");
        layouter.print(" ");
        if (x.getLabel() != null) {
            x.getLabel().visit(this);
        }
    }

    @Override
    public void performActionOnCcatchBreakWildcardParameterDeclaration(
            CcatchBreakWildcardParameterDeclaration x) {
        layouter.keyWord("\\Break");
        layouter.print(" *");
    }

    @Override
    public void performActionOnCcatchContinueWildcardParameterDeclaration(
            CcatchContinueWildcardParameterDeclaration x) {
        layouter.keyWord("\\Continue");
    }

    /**
     * Prints the JML assert statement.
     *
     * @param jmlAssert the statement to print
     */
    @Override
    public void performActionOnJmlAssert(JmlAssert jmlAssert) {
        layouter.print("//@ ");
        final String kind = jmlAssert.getKind().name().toLowerCase();
        layouter.keyWord(kind);

        layouter.beginRelativeC();
        layouter.brk();

        if (services == null) {
            layouter.print(jmlAssert.getCondition().getText().trim());
        } else {
            var spec = services.getSpecificationRepository().getStatementSpec(jmlAssert);
            if (spec == null) {
                layouter.print(jmlAssert.getCondition().getText().trim());
            } else {
                Term t = spec.term(JmlAssert.INDEX_CONDITION);
                String text = printInLogicPrinter(t);
                layouter.print(text);
            }
        }
        layouter.end();
    }

    /**
     * Prints a JML set statement
     *
     * @param x the set statement
     */
    public void performActionOnSetStatement(SetStatement x) {
        layouter.print("//@ ");
        layouter.keyWord("set");

        layouter.beginRelativeC();
        layouter.brk();

        if (services != null) {
            var spec =
                Objects.requireNonNull(services.getSpecificationRepository().getStatementSpec(x));
            Term target = spec.term(SetStatement.INDEX_TARGET);
            Term value = spec.term(SetStatement.INDEX_VALUE);
            layouter.print(printInLogicPrinter(target));
            layouter.print(" = ");
            layouter.print(printInLogicPrinter(value));
        } else {
            var context = x.getParserContext();
            if (context != null) {
                // remove all whitespaces (\n\f\t...) with an empty space
                var text = context.getText();
                text = text.substring(4, text.length() - 1);
                layouter.print(text);
            }
        }
        layouter.end();
    }

    public String printInLogicPrinter(Term t) {
        var lp = LogicPrinter.quickPrinter(services, usePrettyPrinting, useUnicodeSymbols);
        lp.printTerm(t);
        return lp.result();
    }

}
