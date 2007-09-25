package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;
import java.util.Iterator;
import java.util.List;

import cetus.hir.Expression;
import de.uka.ilkd.key.logic.op.ProgramSV;

public class MetaExpression extends Expression {
        private String name;

        private List arguments;

        public MetaExpression(String name, List arguments) {
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
                return new MetaExpression(name, arguments);
        }

        public void print(OutputStream stream) {
                // TODO: doesn't work with encodings in general
                PrintStream p = new PrintStream(stream);
                p.print(":expr:");
                p.print(name);
                p.print("(");
                for (Iterator i = arguments.iterator(); i.hasNext();)
                        p.print(((ProgramSV) i.next()).name());
                p.print(")");
        }

}
