package org.key_project.jmlediting.core.utilities;

import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.dom.ITypeBinding;

public class JavaElementIdentifier {
   /**
    * The name of the identified element.
    */
   private final String name;
   /**
    * The resolved type of the identified Element.
    */
   private final ITypeBinding type;
   /**
    * The declaringClass of the identified Element.
    */
   private final IType declaringClass;

   /**
    * Creates a new JavaElementIdentifier that is used to uniquely identify a
    * JavaElement.
    *
    * @param name
    *           the name of the Element
    * @param type
    *           the type of the Element
    * @param declaringClass
    *           the declaring Class of the Element
    */
   public JavaElementIdentifier(final String name, final ITypeBinding type,
         final IType declaringClass) {
      this.name = name;
      this.type = type;
      this.declaringClass = declaringClass;
   }

   /**
    * @return the name
    */
   public String getName() {
      return this.name;
   }

   /**
    * @return the type
    */
   public ITypeBinding getType() {
      return this.type;
   }

   /**
    * @return the declaringClass
    */
   public IType getDeclaringClass() {
      return this.declaringClass;
   }

}
