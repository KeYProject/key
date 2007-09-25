package de.uka.ilkd.key.lang.clang.common.type.declaration;


/**
 * C program structured type declaration.
 * 
 * @author oleg.myrk@gmail.com
 */
public abstract class StructuredTypeDecl {
        /**
         * Id of the structured type
         */
        private final String id;
        
        /**
         * A map from member names to the member declarations.
         */
        private final HashMapFromStringToMemberDecl memberMap = new HashMapFromStringToMemberDecl();
        
        /**
         * A flag that tells if the members have been defined already.
         */
        boolean membersDefined = false;
        
        /**
         * Creates structured type declaration with given id. Its members can be created
         * and modified through the accessor functions. 
         * @param id id to use
         */
        protected StructuredTypeDecl(String id) {
                this.id = id;
        }
        
        /**
         * Returns id of the structured type.
         * @return id
         */
        public String getId() {
                return id;
        }
        
        /**
         * Returns the member map.
         *
         * @return member map
         */
        public HashMapFromStringToMemberDecl getMemberMap() {
                return memberMap;
        }
        
        /**
         * Tells whether the members have already been defined. 
         * Initially <code>false</code>.
         * @return
         */
        public boolean getMembersDefined() {
                return membersDefined;
        }
        
        /**
         * Sets the flag "members defined" to <code>true</code>. Do not modify
         * or add new members after calling this method.
         */
        public void setMembersDefined() {
                membersDefined = true;
        }
        
        /**
         * Template method to format structured type declaration's header
         * @return formatted header
         */
        public abstract String formatHeader();
        
        public String toString() {
                StringBuffer buffer = new StringBuffer();
                buffer.append(this.formatHeader());
                buffer.append("{");
                for(IteratorOfMemberDecl i = memberMap.values(); i.hasNext();) {
                        MemberDecl memberDecl = i.next();
                        buffer.append(memberDecl.getId());
                        buffer.append(" : ");
                        buffer.append(memberDecl.getType().getName());
                }
                return buffer.toString();
        }
}
