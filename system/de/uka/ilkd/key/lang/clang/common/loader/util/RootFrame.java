package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.Method;

import cetus.hir.CompoundStatement;
import cetus.hir.Tools;

public class RootFrame extends CompoundStatement {
        private static Method class_print_method;

        static
        {
          Class[] params = new Class[2];

          try {
            params[0] = RootFrame.class;
            params[1] = OutputStream.class;
            class_print_method = params[0].getMethod("defaultPrint", params);
          } catch (NoSuchMethodException e) {
            throw new InternalError();
          }
        }

        /**
         * Prints a statement to a stream.
         *
         * @param stmt The statement to print.
         * @param stream The stream on which to print the statement.
         */
        public static void defaultPrint(RootFrame stmt, OutputStream stream)
        {
          PrintStream p = new PrintStream(stream);
          Tools.printlnList(stmt.children, stream);
        }

        static public void setClassPrintMethod(Method m)
        {
          class_print_method = m;
        }        
}
