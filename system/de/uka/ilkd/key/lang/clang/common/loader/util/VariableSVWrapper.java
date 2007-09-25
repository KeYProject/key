package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;

import cetus.hir.IDExpression;
import de.uka.ilkd.key.lang.clang.common.programsv.VariableProgramSV;

public class VariableSVWrapper extends IDExpression {
        private VariableProgramSV variableSV;

        public VariableSVWrapper(VariableProgramSV variableSV) {
                super(false);
                this.variableSV = variableSV;
        }

        public VariableProgramSV getSV() {
                return variableSV;
        }

        public Object deepClone() {
                return new VariableSVWrapper(variableSV);
        }

        public void print(OutputStream stream) {
                // TODO: doesn't work with encodings in general                
                PrintStream p = new PrintStream(stream);
                p.print(variableSV.name());
        }
}
