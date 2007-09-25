package de.uka.ilkd.key.lang.clang.common.pprinter;

import java.io.IOException;

import de.uka.ilkd.key.lang.clang.common.dispatch.IClangDispatchableProgramElement;
import de.uka.ilkd.key.lang.clang.common.dispatch.IClangProgramDispatcher;
import de.uka.ilkd.key.lang.clang.common.program.declaration.VariableDeclaration;
import de.uka.ilkd.key.lang.clang.common.program.expression.literal.IntegerLiteral;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.AddressOf;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ArrayAccess;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.Comma;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.Conditional;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.Dereference;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.Equals;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberAccess;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberPointerAccess;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.MemberReference;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.NotEquals;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.Parentheses;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ReferenceAssignment;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.TypeCast;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueAssignment;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.ValueOf;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.DecrementPostfix;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.DecrementPrefix;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Divide;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.IncrementPostfix;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.IncrementPrefix;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Minus;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Modulus;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Multiply;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Negative;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Plus;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.arithmetic.Positive;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic.And;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic.Not;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.logic.Or;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory.Calloc;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory.Free;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.memory.Malloc;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.Greater;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.GreaterEq;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.Less;
import de.uka.ilkd.key.lang.clang.common.program.expression.operator.relational.LessEq;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangExpression;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangMemberReference;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangTypeReference;
import de.uka.ilkd.key.lang.clang.common.program.iface.IClangVariable;
import de.uka.ilkd.key.lang.clang.common.program.statement.AllocateStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.BlockFrame;
import de.uka.ilkd.key.lang.clang.common.program.statement.Branch;
import de.uka.ilkd.key.lang.clang.common.program.statement.CompoundStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.ContextFrame;
import de.uka.ilkd.key.lang.clang.common.program.statement.DestroyStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.ExpressionStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.FrameBody;
import de.uka.ilkd.key.lang.clang.common.program.statement.IfStatement;
import de.uka.ilkd.key.lang.clang.common.program.statement.RootFrame;
import de.uka.ilkd.key.lang.clang.common.program.statement.WhileStatement;
import de.uka.ilkd.key.lang.clang.common.program.type.TypeReference;
import de.uka.ilkd.key.lang.clang.common.program.variable.Variable;
import de.uka.ilkd.key.lang.clang.common.programmeta.IClangProgramMeta;
import de.uka.ilkd.key.lang.clang.common.programsv.BaseClangProgramSV;
import de.uka.ilkd.key.lang.clang.common.type.IClangType;
import de.uka.ilkd.key.lang.clang.common.type.IClangValueType;
import de.uka.ilkd.key.lang.clang.common.type.object.ArrayType;
import de.uka.ilkd.key.lang.clang.common.type.object.ScalarType;
import de.uka.ilkd.key.lang.clang.common.type.object.StructType;
import de.uka.ilkd.key.lang.clang.common.type.object.VoidType;
import de.uka.ilkd.key.lang.clang.common.type.value.ArithmeticType;
import de.uka.ilkd.key.lang.clang.common.type.value.PointerType;
import de.uka.ilkd.key.lang.common.pprinter.BaseProgramPrinter;
import de.uka.ilkd.key.lang.common.pprinter.IProgramPrinter;
import de.uka.ilkd.key.lang.common.program.IProgramElement;
import de.uka.ilkd.key.lang.common.programsv.BaseProgramSV;

/**
 * Program printer of C program elements implementing the double dispatch
 * pattern.
 * 
 * @author oleg.myrk@gmail.com
 */
public class ClangProgramPrinter extends BaseProgramPrinter implements
                IClangProgramDispatcher, IProgramPrinter {
        
        public void print(IProgramElement programElement) throws java.io.IOException {
                if (!(programElement instanceof IClangDispatchableProgramElement))
                        throw new IllegalStateException(
                                        "ClangProgramPrinter applied to language specific source element that is not IClangPrintableSourceElement");
                try {
                        dispatch((IClangDispatchableProgramElement)programElement);
                }
                catch(Exception e) {
                        if (e instanceof IOException)
                                throw (IOException)e;
                        else
                                throw new RuntimeException(e);
                }
        }
        
        public void dispatch(IClangDispatchableProgramElement x) throws Exception {
                x.dispatch(this);
        }

        public void dispatchCompoundStatement(CompoundStatement x)
                        throws Exception {
                printHeader(x);

                if (x.getStatementCount() > 0) {
                        markStart(0, x);
                        writeToken("{", x);
                        writeLineList(1, +1, 0, x.getStatements());
                        writeSymbol(1, -1, "}");
                        markEnd(0, x);
                } else {
                        markStart(0, x);
                        writeToken("{}", x);
                        markEnd(0, x);
                }

                printFooter(x);
        }

        public void dispatchBlockFrame(BlockFrame x) throws Exception {
                printHeader(x);

                if (x.getBody().getStatements().size() > 0) {
                        writeToken("", x);
                        write("block-frame(");
                        writeCommaList(x.getVariables());
                        write(") {");
                        writeLineList(1, +1, 0, x.getBody().getStatements());
                        writeSymbol(1, -1, "}");
                } else {
                        markStart(0, x);
                        writeToken("", x);
                        write("block-frame(");
                        writeCommaList(x.getVariables());
                        write(") {}");
                        markEnd(0, x);
                }

                printFooter(x);
        }

        public void dispatchRootFrame(RootFrame x) throws Exception {
                printHeader(x);

                if (x.getBody().getStatements().size() > 0) {
                        writeToken("", x);
                        writeLineList(1, 1, 0, x.getBody().getStatements());
                        writeSymbol(1, -1, "");
                } else {
                        markStart(0, x);
                        writeToken(" ", x);
                        markEnd(0, x);
                }

                printFooter(x);
        }

        public void dispatchFrameBody(FrameBody x) throws Exception {
                printHeader(x);

                if (x.getStatements().size() > 0) {
                        write("frame {");
                        writeLineList(1, +1, 0, x.getStatements());
                        writeSymbol(1, -1, "}");
                } else {
                        write("{}");
                }

                printFooter(x);
        }

        public void dispatchContextFrame(ContextFrame x) throws Exception {
                printHeader(x);

                if (x.getStatements().size() > 0) {
                        writeToken(".. ", x);
                        writeLineList(1, +1, 0, x.getStatements());
                        writeSymbol(1, -1, " ...");
                } else {
                        markStart(0, x);
                        writeToken(".. ...", x);
                        markEnd(0, x);
                }

                printFooter(x);
        }

        public void dispatchExpressionStatement(ExpressionStatement x)
                        throws Exception {
                writeIndentation(x);
                printHeader(x);
                markStart(0, x);
                writeElement(x.getExpression());
                write(";");
                markEnd(0, x);
                printFooter(x);
        }

        public void dispatchAllocateStatement(AllocateStatement x)
                        throws Exception {
                writeIndentation(x);
                printHeader(x);
                markStart(0, x);
                writeToken("allocate ", x);
                writeElement(x.getExpression());
                write(";");
                markEnd(0, x);
                printFooter(x);
        }

        public void dispatchIfStatement(IfStatement x) throws Exception {
                writeIndentation(x);
                printHeader(x);
                markStart(0, x);
                writeToken("if (", x);
                writeElement(x.getCondition());
                write(") ");
                writeElement(1, 0, x.getThenBranch());
                if (x.getElseBranch() != null) {
                        writeSymbol(1, 0, "else ");
                        writeElement(1, 0, x.getElseBranch());
                }
                markEnd(0, x);
                printFooter(x);
        }

        public void dispatchWhileStatement(WhileStatement x) throws Exception {
                writeIndentation(x);
                printHeader(x);
                markStart(0, x);
                writeToken("while (", x);
                writeElement(x.getCondition());
                write(") ");
                writeElement(1, 0, x.getBody());
                markEnd(0, x);
                printFooter(x);
        }

        public void dispatchBranch(Branch x) throws Exception {
                writeIndentation(x);
                printHeader(x);
                if (x.getBody() instanceof CompoundStatement)
                        writeElement(x.getBody());
                else {
                        writeElement(0, 1, x.getBody());
                        changeLevel(-1);
                }
                printFooter(x);
        }

        public void dispatchDestroyStatement(DestroyStatement x)
                        throws Exception {
                writeIndentation(x);
                printHeader(x);
                markStart(0, x);
                writeToken("destroy ", x);
                writeElement(x.getExpression());
                write(";");
                markEnd(0, x);
                printFooter(x);
        }

        public void dispatchVariableDeclaration(VariableDeclaration x)
                        throws Exception {
                // Collect data
                IClangTypeReference typeReference = x.getTypeReference();
                IClangVariable variable = x.getVariable();
                IClangExpression initializer = x.getInitializer();
                boolean isStatic = x.getIsStatic();

                StringBuffer specifier = new StringBuffer();
                StringBuffer declarator = new StringBuffer();

                // If schema declaration
                if (typeReference instanceof BaseProgramSV) {
                        if (isStatic)
                                specifier.append("static ");

                        specifier.append(((BaseProgramSV) typeReference)
                                        .getName());

                        declarator.append(((BaseProgramSV) variable).getName());
                }
                // If non-schema declaration
                else {
                        // Collect data
                        IClangType type = (IClangType) typeReference
                                        .getTypePair().getJavaType();

                        boolean isRegister = type instanceof IClangValueType;

                        if (isStatic)
                                specifier.append("static ");
                        if (isRegister) {
                                specifier.append("register ");
                        }

                        // Format
                        declarator.append(variable.name());

                        boolean lastDeclaratorWasPointer = false;
                        while (true) {
                                if (type instanceof ArithmeticType
                                                || type instanceof StructType
                                                || type instanceof VoidType) {
                                        specifier.append(type.getName());
                                        break;
                                }

                                if (type instanceof ScalarType) {
                                        type = ((ScalarType) type)
                                                        .getValueType();
                                } else if (type instanceof PointerType) {
                                        declarator.insert(0, "*");
                                        type = ((PointerType) type)
                                                        .getTargetType();
                                        lastDeclaratorWasPointer = true;
                                } else if (type instanceof ArrayType) {
                                        if (lastDeclaratorWasPointer) {
                                                declarator.insert(0, "(");
                                                declarator.append(")");
                                        }

                                        declarator.append("[");
                                        declarator.append(((ArrayType) type)
                                                        .getSize());
                                        declarator.append("]");

                                        type = ((ArrayType) type).getElemType();
                                        lastDeclaratorWasPointer = false;
                                }
                        }
                }

                // Output
                writeIndentation(x);
                printHeader(x);
                markStart(0, x);
                write(specifier.toString());
                write(" ");
                write(declarator.toString());
                if (initializer != null) {
                        write(" = ");
                        writeElement(initializer);
                }
                write(";");
                markEnd(0, x);
                printFooter(x);
        }

        public void dispatchModifier(VariableDeclaration.Modifier x)
                        throws Exception {
                printHeader(x);
                write(x.getModifierName());
                printFooter(x);
        }

        public void dispatchTypeReference(TypeReference x) throws Exception {
                StringBuffer specifier = new StringBuffer();
                StringBuffer declarator = new StringBuffer();

                // Collect data
                IClangType type = (IClangType) x.getTypePair().getJavaType();

                // Format
                boolean lastDeclaratorWasPointer = false;
                while (true) {
                        if (type instanceof ArithmeticType
                                        || type instanceof StructType
                                        || type instanceof VoidType) {
                                specifier.append(type.getName());
                                break;
                        }

                        if (type instanceof ScalarType) {
                                type = ((ScalarType) type).getValueType();
                        } else if (type instanceof PointerType) {
                                declarator.insert(0, "*");
                                type = ((PointerType) type).getTargetType();
                                lastDeclaratorWasPointer = true;
                        } else if (type instanceof ArrayType) {
                                if (lastDeclaratorWasPointer) {
                                        declarator.insert(0, "(");
                                        declarator.append(")");
                                }

                                declarator.append("[");
                                declarator.append(((ArrayType) type).getSize());
                                declarator.append("]");

                                type = ((ArrayType) type).getElemType();
                                lastDeclaratorWasPointer = false;
                        }
                }

                // Output
                write(specifier.toString());
                write(declarator.toString());
        }

        public void dispatchVariable(Variable x) throws Exception {
                printHeader(x);
                write(x.name().toString());
                printFooter(x);
        }

        public void dispatchAddressOf(AddressOf x) throws Exception {
                printHeader(x);
                write("&");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchDereference(Dereference x) throws Exception {
                printHeader(x);
                write("*");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchValueOf(ValueOf x) throws Exception {
                printHeader(x);
                // Useful for debugging: 
                // write("@");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchMemberReference(MemberReference x) throws Exception {
                printHeader(x);
                writeInternalIndentation(x);
                write(x.getMemberName().toString());
                printFooter(x);
        }

        public void dispatchMemberAccess(MemberAccess x) throws Exception {
                printHeader(x);
                writeElement(x.getExpression());
                writeToken(".", x);
                IClangMemberReference memberReference = x.getMemberReference();
                if (memberReference instanceof BaseProgramSV)
                        writeToken(((BaseProgramSV) memberReference).name()
                                        .toString(), x);
                else
                        writeToken(memberReference.getMemberName().toString(),
                                        x);
                printFooter(x);
        }

        public void dispatchMemberPointerAccess(MemberPointerAccess x)
                        throws Exception {
                printHeader(x);
                writeElement(x.getExpression());
                writeToken("->", x);
                IClangMemberReference memberReference = x.getMemberReference();
                if (memberReference instanceof BaseProgramSV)
                        writeToken(((BaseProgramSV) memberReference).name()
                                        .toString(), x);
                else
                        writeToken(memberReference.getMemberName().toString(),
                                        x);
                printFooter(x);
        }

        public void dispatchArrayAccess(ArrayAccess x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("[");
                writeElement(x.getExpressionAt(1));
                write("]");
                printFooter(x);
        }

        public void dispatchReferenceAssignment(ReferenceAssignment x)
                        throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("<-");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchValueAssignment(ValueAssignment x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("=");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchEquals(Equals x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("==");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchNotEquals(NotEquals x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("!=");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchPlus(Plus x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("+");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchMinus(Minus x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("-");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchMultiply(Multiply x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("*");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchDivide(Divide x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("/");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchModulus(Modulus x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("%");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchNegative(Negative x) throws Exception {
                printHeader(x);
                write("-");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchPositive(Positive x) throws Exception {
                printHeader(x);
                write("+");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchIncrementPostfix(IncrementPostfix x)
                        throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("++");
                printFooter(x);
        }

        public void dispatchIncrementPrefix(IncrementPrefix x)
                        throws Exception {
                printHeader(x);
                write("++");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchDecrementPostfix(DecrementPostfix x)
                        throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("--");
                printFooter(x);
        }

        public void dispatchDecrementPrefix(DecrementPrefix x)
                        throws Exception {
                printHeader(x);
                write("--");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchAnd(And x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("&&");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchOr(Or x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("||");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchNot(Not x) throws Exception {
                printHeader(x);
                write("!");
                writeElement(x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchLess(Less x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("<");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchLessEq(LessEq x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write("<=");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchGreater(Greater x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write(">");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchGreaterEq(GreaterEq x) throws Exception {
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write(">=");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchConditional(Conditional x) throws Exception {
                printHeader(x);
                writeElement(0, x.getExpressionAt(0));
                write(" ?");
                writeElement(1, x.getExpressionAt(1));
                write(" :");
                writeElement(1, x.getExpressionAt(2));
                printFooter(x);
        }

        public void dispatchComma(Comma x) throws Exception {
                // TODO: add brackets when needed
                printHeader(x);
                writeElement(x.getExpressionAt(0));
                write(",");
                writeElement(x.getExpressionAt(1));
                printFooter(x);
        }

        public void dispatchIntLiteral(IntegerLiteral x) throws Exception {
                printHeader(x);
                write(x.getValue().toString());
                printFooter(x);
        }

        public void dispatchParentheses(Parentheses x) throws Exception {
                printHeader(x);
                writeToken("(", x);
                writeElement(x.getExpressionAt(0));
                write(")");
                printFooter(x);
        }

        public void dispatchTypeCast(TypeCast x) throws Exception {
                printHeader(x);
                write("(");
                writeElement(0, x.getTypeReference());
                write(")");
                writeElement(0, x.getExpressionAt(0));
                printFooter(x);
        }

        public void dispatchMalloc(Malloc x) throws Exception {
                printHeader(x);
                write("malloc(sizeof(");
                writeElement(0, x.getTypeReference());
                write("))");
                printFooter(x);
        }

        public void dispatchCalloc(Calloc x) throws Exception {
                printHeader(x);
                write("calloc(");
                writeElement(0, x.getExpressionAt(0));
                write(", sizeof(");
                writeElement(0, x.getTypeReference());
                write("))");
                printFooter(x);
        }

        public void dispatchFree(Free x) throws Exception {
                printHeader(x);
                write("free(");
                writeElement(0, x.getExpressionAt(0));
                write(")");
                printFooter(x);
        }

        public void dispatchProgramMeta(IClangProgramMeta x)
                        throws Exception {
                printHeader(x);
                write(x.name().toString());
                write("(");
                if (x.getArguments().size() != 0)
                        writeCommaList(0, x.getArguments());
                write(")");
                printFooter(x);
        }

        public void dispatchProgramSV(BaseClangProgramSV x) throws Exception {
                markStart(0, x);
                printHeader(x);
                writeInternalIndentation(x);
                write(x.name().toString());
                printFooter(x);
                markEnd(0, x);
        }
}
