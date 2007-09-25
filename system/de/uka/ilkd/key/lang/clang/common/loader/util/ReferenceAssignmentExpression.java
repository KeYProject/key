package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.*;
import java.lang.reflect.*;
import java.util.*;

import cetus.hir.AssignmentExpression;
import cetus.hir.AssignmentOperator;
import cetus.hir.BinaryOperator;
import cetus.hir.Expression;
import cetus.hir.Printable;

public class ReferenceAssignmentExpression extends cetus.hir.BinaryExpression
{
        private static Method class_print_method;

        static
        {
          Class[] params = new Class[2];

          try {
            params[0] = ReferenceAssignmentExpression.class;
            params[1] = OutputStream.class;
            class_print_method = params[0].getMethod("defaultPrint", params);
          } catch (NoSuchMethodException e) {
            throw new InternalError();
          }
        }

        /**
         * Creates a reference assignment expression.
         *
         * @param lhs The lefthand expression.
         * @param op An assignment operator.
         * @param rhs The righthand expression.
         */
        public ReferenceAssignmentExpression(Expression lhs, Expression rhs)
        {
          super(lhs, ReferenceAssignmentOperator.REFERENCE_ASSIGNMENT, rhs);
          object_print_method = class_print_method;
        }

        public Object clone()
        {
          return (ReferenceAssignmentExpression)super.clone();
        }

        /**
         * Prints a reference assignment expression to a stream.
         *
         * @param expr The expression to print.
         * @param stream The stream on which to print the expression.
         */
        public static void defaultPrint(ReferenceAssignmentExpression expr, OutputStream stream)
        {
          PrintStream p = new PrintStream(stream);

          ((Printable)expr.children.get(0)).print(stream);
          expr.op.print(stream);
          ((Printable)expr.children.get(1)).print(stream);
        }

        /**
         * Overrides the class print method, so that all subsequently
         * created objects will use the supplied method.
         *
         * @param m The new print method.
         */
        static public void setClassPrintMethod(Method m)
        {
          class_print_method = m;
        }
}
