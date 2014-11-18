package org.key_project.jmlediting.core.profile;

import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

public class ConfigurableJMLProfile implements IJMLProfile {
   
   private String name;
   private String identifier;
   private Set<IJMLBehaviorSpecification> supportedBehaviors;
   private Set<IJMLGenericSpecification> supportedGenerics;
   
   public ConfigurableJMLProfile(String name, String identifier) {
      super();
      this.name = name;
      this.identifier = identifier;
      this.supportedBehaviors = new HashSet<IJMLBehaviorSpecification>();
      this.supportedGenerics = new HashSet<IJMLGenericSpecification>();
   }

   @Override
   public String getName() {
      return this.name;
   }

   @Override
   public String getIdentifier() {
      return this.identifier;
   }

   @Override
   public Set<IJMLBehaviorSpecification> getSupportedBehaviors() {
      return this.supportedBehaviors;
   }

   @Override
   public Set<IJMLGenericSpecification> getSupportedGenerics() {
      return this.supportedGenerics;
   }
   
   public void addSupportGeneric(IJMLGenericSpecification spec) {
      if (spec == null) {
         throw new NullPointerException("Cannot add a null specification");
      }
      this.supportedGenerics.add(spec);
   }
   
   public boolean removeSupportedGeneric(IJMLGenericSpecification spec) {
      return this.supportedGenerics.remove(spec);
   }
   
   public void addSupportedBehavior(IJMLBehaviorSpecification spec) {
      if (spec == null) {
         throw new NullPointerException("Cannot add a null specification");    
      }
      this.supportedBehaviors.add(spec);
   }
   
   public boolean removeSupportedBehavior(IJMLBehaviorSpecification spec) {
      return this.supportedBehaviors.remove(spec);
   }

}
