package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;

import cetus.hir.Specifier;
import de.uka.ilkd.key.lang.clang.common.programsv.TypeProgramSV;

public class TypeSVWrapper extends Specifier {
        protected TypeProgramSV typeSV;

        public TypeSVWrapper(TypeProgramSV typeSV) {
                super(4);
                this.typeSV = typeSV;
        }

        public TypeProgramSV getSV() {
                return typeSV;
        }

        public Object deepClone() {
                return new TypeSVWrapper(typeSV);
        }

        public void print(OutputStream stream) {
                // TODO: doesn't work with encodings in general
                PrintStream p = new PrintStream(stream);
                p.print(typeSV.name());
        }        
}
