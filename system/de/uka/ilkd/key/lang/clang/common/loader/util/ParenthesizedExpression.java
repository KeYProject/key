package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.Method;

import cetus.hir.Expression;
import cetus.hir.Printable;

public class ParenthesizedExpression extends cetus.hir.UnaryExpression
{
        private static Method class_print_method;

        static
        {
          Class[] params = new Class[2];

          try {
            params[0] = ParenthesizedExpression.class;
            params[1] = OutputStream.class;
            class_print_method = params[0].getMethod("defaultPrint", params);
          } catch (NoSuchMethodException e) {
            throw new InternalError();
          }
        }

        /**
         * Creates a parenthesized expression.
         *
         * @param expression
         */
        public ParenthesizedExpression(Expression expression)
        {
          super(ParenthesesOperator.PARENTHESES, expression);
          object_print_method = class_print_method;
        }

        public Object clone()
        {
          return (ParenthesizedExpression)super.clone();
        }

        /**
         * Prints a parenthesized expression to a stream.
         *
         * @param expr The expression to print.
         * @param stream The stream on which to print the expression.
         */
        public static void defaultPrint(ParenthesizedExpression expr, OutputStream stream)
        {
          PrintStream p = new PrintStream(stream);

          p.print("(");
          ((Printable)expr.children.get(0)).print(stream);
          p.print(")");
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
