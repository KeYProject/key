package de.uka.ilkd.key.lang.clang.common.type.declaration;

import de.uka.ilkd.key.lang.clang.common.type.IClangInstantiableObjectType;

/**
 * C program structured type member declaration.
 * 
 * @author oleg.myrk@gmail.com
 */
public class MemberDecl {
        private String id;
        private IClangInstantiableObjectType type;
        private int order;
        
        /**
         * Creates structured type member declaration with given id and type. 
         * @param id id to use
         * @param type object type to use
         */
        public MemberDecl(String id, IClangInstantiableObjectType type, int order) {
                this.id = id;
                this.type = type;
                this.order = order;
        }
        
        /**
         * Returns the id of the member.
         * @return id
         */
        public String getId() {
                return id;
        }
        
        /**
         * Returns the type of the member.
         * @return id
         */
        public IClangInstantiableObjectType getType() {
                return type;
        }
        
        /**
         * Returns the order index of the member.
         * @return
         */
        public int getOrder() {
                return order;
        }
}
