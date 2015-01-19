package org.key_project.key4eclipse.resources.io;

public class ProofMetaReferenceAccess {

   private String kjt;
   private String name;
   private String type;
   private String visibility;
   private boolean isStatic;
   private boolean isFinal;
   private boolean assignedInConstructor;
   private String initializer;
   
   public ProofMetaReferenceAccess(String kjt, String name, String type, String visibility, boolean isStatic, boolean isFinal, boolean assignedInConstructor, String initializer){
      this.kjt = kjt;
      this.name = name;
      this.type = type;
      this.visibility = visibility;
      this.isStatic = isStatic;
      this.isFinal = isFinal;
      this.assignedInConstructor = assignedInConstructor;
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

   public boolean isCalledInConstructor() {
      return assignedInConstructor;
   }

   public String getInitializer() {
      return initializer;
   }
   
}
