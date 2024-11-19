package de.uka.ilkd.key.java.recoderext.mst;

import de.uka.ilkd.key.java.recoderext.adt.ADTPrefixConstruct;
import recoder.java.Expression;

public class MSetIntersect extends ADTPrefixConstruct{

        /**
         *
         */
        private static final long serialVersionUID = 8877658515734186914L;


        public MSetIntersect(Expression lhs, Expression rhs) {
            super(lhs, rhs);
            makeParentRoleValid();
        }


        protected MSetIntersect(de.uka.ilkd.key.java.recoderext.mst.MSetIntersect proto) {
            super(proto);
            makeParentRoleValid();
        }


        @Override
        public de.uka.ilkd.key.java.recoderext.mst.MSetIntersect deepClone() {
            return new de.uka.ilkd.key.java.recoderext.mst.MSetIntersect(this);
        }


        @Override
        public int getArity() {
            return 2;
        }


        @Override
        public int getNotation() {
            return PREFIX;
        }
    }





