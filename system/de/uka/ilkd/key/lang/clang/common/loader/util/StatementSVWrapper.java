package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;

import cetus.hir.Statement;
import de.uka.ilkd.key.lang.clang.common.programsv.StatementProgramSV;

public class StatementSVWrapper extends Statement {
        protected StatementProgramSV statementSV;

        public StatementSVWrapper(StatementProgramSV statementSV) {
                this.statementSV = statementSV;
        }

        public StatementProgramSV getSV() {
                return statementSV;
        }

        public Object deepClone() {
                return new StatementSVWrapper(statementSV);
        }

        public void print(OutputStream stream) {
                // TODO: doesn't work with encodings in general
                PrintStream p = new PrintStream(stream);
                p.print(statementSV.name());
        }
        
}
