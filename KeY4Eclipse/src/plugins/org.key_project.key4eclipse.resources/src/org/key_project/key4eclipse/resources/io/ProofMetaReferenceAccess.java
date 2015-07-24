package org.key_project.key4eclipse.resources.io;

/**
 * Represents an access reference for the ProofMetaReferences
 * @author Stefan Käsdorf
 */
public class ProofMetaReferenceAccess {

   private String kjt;
   private String name;
   private String type;
   private String visibility;
   private boolean isStatic;
   private boolean isFinal;
   private String initializer;
   
   public ProofMetaReferenceAccess(String kjt, String name, String type, String visibility, boolean isStatic, boolean isFinal, String initializer){
      this.kjt = kjt;
      this.name = name;
      this.type = type;
      this.visibility = visibility;
      this.isStatic = isStatic;
      this.isFinal = isFinal;
      this.initializer = initializer;
   }

   public String getKjt() {
      return kjt;
   }

   public String getName() {
      return name;
   }
   
   public String getType() {
      return type;
   }

   public String getVisibility() {
      return visibility;
   }

   public boolean isStatic() {
      return isStatic;
   }

   public boolean isFinal() {
      return isFinal;
   }

   public String getInitializer() {
      return initializer;
   }
   
}
