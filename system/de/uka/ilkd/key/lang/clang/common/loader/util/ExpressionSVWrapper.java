package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;

import cetus.hir.Expression;
import de.uka.ilkd.key.lang.clang.common.programsv.ExpressionProgramSV;
import de.uka.ilkd.key.logic.op.ProgramSV;

public class ExpressionSVWrapper extends Expression {

        private ExpressionProgramSV expressionSV;

        public ExpressionSVWrapper(ExpressionProgramSV expressionSV) {
                this.expressionSV = expressionSV;
        }

        public ExpressionProgramSV getSV() {
                return expressionSV;
        }

        public Object deepClone() {
                return new ExpressionSVWrapper(expressionSV);
        }

        public void print(OutputStream stream) {
                // TODO: doesn't work with encodings in general 
                PrintStream p = new PrintStream(stream);
                p.print(expressionSV.name());
        }
}
