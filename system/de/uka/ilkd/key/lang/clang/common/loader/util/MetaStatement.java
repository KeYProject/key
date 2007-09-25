package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;
import java.lang.reflect.Method;
import java.util.Iterator;
import java.util.List;

import cetus.hir.Statement;
import de.uka.ilkd.key.logic.op.ProgramSV;

public class MetaStatement extends Statement {
        private static Method class_print_method;

        static
        {
          Class[] params = new Class[2];

          try {
            params[0] = MetaStatement.class;
            params[1] = OutputStream.class;
            class_print_method = params[0].getMethod("defaultPrint", params);
          } catch (NoSuchMethodException e) {
            throw new InternalError();
          }
        }

        private String name;
        private List arguments;

        public MetaStatement(String name, List arguments) {
                object_print_method = class_print_method;

                this.name = name;
                this.arguments = arguments;
        }

        public String getName() {
                return name;
        }

        public List getArguments() {
                return arguments;
        }

        public Object deepClone() {
                return new MetaStatement(name, arguments);
        }

        public static void defaultPrint(MetaStatement stmnt, OutputStream stream) {
                // TODO: doesn't work with encodings in general
                PrintStream p = new PrintStream(stream);
                p.print(":stmnt:");
                p.print(stmnt.name);
                p.print("(");
                for(Iterator i = stmnt.arguments.iterator(); i.hasNext();) 
                        p.print(((ProgramSV)i.next()).name());
                p.print(")");
        }

        static public void setClassPrintMethod(Method m)
        {
          class_print_method = m;
        }
}
