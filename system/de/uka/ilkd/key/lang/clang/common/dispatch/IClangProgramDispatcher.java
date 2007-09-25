package de.uka.ilkd.key.lang.clang.common.dispatch;

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

/**
 * A dispatcher of C program elements implementing double dispatch pattern.
 * 
 * @author oleg.myrk@gmail.com
 */
public interface IClangProgramDispatcher {
        
        void dispatchCompoundStatement(CompoundStatement pe) throws Exception;

        void dispatchFrameBody(FrameBody pe) throws Exception;

        void dispatchBlockFrame(BlockFrame pe) throws Exception;

        void dispatchRootFrame(RootFrame pe) throws Exception;

        void dispatchContextFrame(ContextFrame pe) throws Exception;

        void dispatchVariableDeclaration(VariableDeclaration pe) throws Exception;
        
        void dispatchModifier(VariableDeclaration.Modifier pe) throws Exception;
        
        void dispatchTypeReference(TypeReference pe) throws Exception;
        
        void dispatchExpressionStatement(ExpressionStatement pe) throws Exception;

        void dispatchAllocateStatement(AllocateStatement pe) throws Exception;

        void dispatchDestroyStatement(DestroyStatement pe) throws Exception;
        
        void dispatchIfStatement(IfStatement pe) throws Exception;
        
        void dispatchWhileStatement(WhileStatement pe) throws Exception;
        
        void dispatchBranch(Branch pe) throws Exception;
        
        void dispatchVariable(Variable pe) throws Exception;
        
        void dispatchAddressOf(AddressOf pe) throws Exception;

        void dispatchDereference(Dereference pe) throws Exception;

        void dispatchValueOf(ValueOf pe) throws Exception;
        
        void dispatchMemberReference(MemberReference pe) throws Exception;
        
        void dispatchMemberAccess(MemberAccess pe) throws Exception;

        void dispatchMemberPointerAccess(MemberPointerAccess pe) throws Exception;

        void dispatchArrayAccess(ArrayAccess pe) throws Exception;

        void dispatchReferenceAssignment(ReferenceAssignment pe) throws Exception;

        void dispatchValueAssignment(ValueAssignment pe) throws Exception;

        void dispatchEquals(Equals pe) throws Exception;

        void dispatchNotEquals(NotEquals pe) throws Exception;

        void dispatchPlus(Plus pe) throws Exception;

        void dispatchMinus(Minus pe) throws Exception;

        void dispatchMultiply(Multiply pe) throws Exception;

        void dispatchDivide(Divide pe) throws Exception;

        void dispatchModulus(Modulus pe) throws Exception;

        void dispatchNegative(Negative pe) throws Exception;

        void dispatchPositive(Positive pe) throws Exception;

        void dispatchIncrementPostfix(IncrementPostfix pe)
                        throws Exception;

        void dispatchIncrementPrefix(IncrementPrefix pe) throws Exception;

        void dispatchDecrementPostfix(DecrementPostfix pe)
                        throws Exception;

        void dispatchDecrementPrefix(DecrementPrefix pe) throws Exception;

        void dispatchAnd(And pe) throws Exception;

        void dispatchOr(Or pe) throws Exception;

        void dispatchNot(Not pe) throws Exception;

        void dispatchLess(Less pe) throws Exception;

        void dispatchLessEq(LessEq pe) throws Exception;

        void dispatchGreater(Greater pe) throws Exception;

        void dispatchGreaterEq(GreaterEq pe) throws Exception;

        void dispatchConditional(Conditional pe) throws Exception;

        void dispatchComma(Comma pe) throws Exception;

        void dispatchIntLiteral(IntegerLiteral pe) throws Exception;

        void dispatchParentheses(Parentheses pe) throws Exception;

        void dispatchTypeCast(TypeCast pe) throws Exception;

        void dispatchMalloc(Malloc pe) throws Exception;

        void dispatchCalloc(Calloc pe) throws Exception;

        void dispatchFree(Free pe) throws Exception;
        
        void dispatchProgramMeta(IClangProgramMeta pe) throws Exception;
        
        void dispatchProgramSV(BaseClangProgramSV pe) throws Exception;
}