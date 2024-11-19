package de.uka.ilkd.key.java.recoderext.mst;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;
import de.uka.ilkd.key.java.recoderext.adt.SeqLength;
import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

public class MSetCard extends Operator {


        private static final long serialVersionUID = 0;


        public MSetCard(Expression msetEl) {
            super(msetEl);
            makeParentRoleValid();
        }


        protected MSetCard(de.uka.ilkd.key.java.recoderext.mst.MSetCard proto) {
            super(proto);
            makeParentRoleValid();
        }


        @Override
        public de.uka.ilkd.key.java.recoderext.mst.MSetCard deepClone() {
            return new de.uka.ilkd.key.java.recoderext.mst.MSetCard(this);
        }


        @Override
        public int getArity() {
            return 1;
        }


        @Override
        public int getPrecedence() {
            return 0;
        }


        @Override
        public int getNotation() {
            return POSTFIX;
        }


        @Override
        public void accept(SourceVisitor v) {

        }

        public String toSource() {
            return children.get(0).toSource() + ".length";
        }

    }


