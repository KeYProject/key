package de.uka.ilkd.key.lang.clang.common.type.declaration;

/**
 * C program struct type declaration.
 * 
 * @author oleg.myrk@gmail.com
 */
public class StructDecl extends StructuredTypeDecl {
        /**
         * Creates struct declaration with given id. Its members can be created
         * and modified through the accessor functions.  
         * @param id id to use
         */
        public StructDecl(String id) {
                super(id);
        }
        
        public String formatHeader() {
                return "struct " + getId();
        }
}
