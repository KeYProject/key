package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;


/**
 * Taclets are required to be assigned a unique name. An exception is that two taclets may have the same name if they belong to different taclet options (choices)
 * This class is intended to be used a key for 
 */
public class RuleKey {
   public final Name name;
   public final ImmutableSet<Choice> choices;
   public final Rule r;

   RuleKey(Name name, ImmutableSet<Choice> choices, Rule r) {
      this.name = name;
      this.choices = choices;
      this.r = r;
   }

   public RuleKey(Rule r) {
      this(r.name(), (r instanceof Taclet ? ((Taclet) r).getChoices()
            : DefaultImmutableSet.<Choice> nil()), r);
   }

   public boolean equals(Object o) {
      if (o == null)
         return false;
      if (o == this)
         return true;

      if (o.getClass() != this.getClass())
         return false;

      final RuleKey other = (RuleKey) o;
      return name.equals(other.name) && choices.equals(other.choices);
   }

   public int hashCode() {
      return name.hashCode() * 17 + 7 * choices.hashCode();
   }

   public String toString() {
      return "(" + name + ", " + choices + ")";
   }

}
