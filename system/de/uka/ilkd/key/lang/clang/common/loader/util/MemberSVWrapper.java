package de.uka.ilkd.key.lang.clang.common.loader.util;

import java.io.OutputStream;
import java.io.PrintStream;

import cetus.hir.IDExpression;
import de.uka.ilkd.key.lang.clang.common.programsv.MemberReferenceProgramSV;

public class MemberSVWrapper extends IDExpression {
        private MemberReferenceProgramSV memberSV;

        public MemberSVWrapper(MemberReferenceProgramSV memberSV) {
                super(false);
                this.memberSV = memberSV;
        }

        public MemberReferenceProgramSV getSV() {
                return memberSV;
        }

        public Object deepClone() {
                return new MemberSVWrapper(memberSV);
        }

        public void print(OutputStream stream) {
                // TODO: doesn't work with encodings in general                
                PrintStream p = new PrintStream(stream);
                p.print(memberSV.name());
        }
}
