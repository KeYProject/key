// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.util;

import java.util.Collection;
import java.util.Map;

/**
 * <p>
 * Instances of this class are used to reset overwritten {@link Object#equals(Object)}
 * and {@link Object#hashCode()} methods of the wrapped child element to the
 * default Java implementation with referenced based equality.
 * </p>
 * <p>
 * A possible use case of this class is for instance the usage in {@link Collection}
 * like {@link Map}s. Imagine the following scenario: A {@code Map<Customer, ...>} maps
 * {@code Customer} instances to something. Each customer has a unique ID and {@link Object#equals(Object)}
 * and {@link Object#hashCode()} is overwritten to compare instances by their unique ID.
 * If now a clone of a {@code Customer} instance exists the {@link Map} will return the value object
 * for the original {@code Customer} instance. The {@link Map} can not separate between original and clone.
 * If instead a {@code Map<EqualsHashCodeResetter<Customer>, ...>} is used original and clone are different
 * because the default Java implementation with referenced based equality is used.
 * </p>
 * @author Martin Hentschel
 */
public class EqualsHashCodeResetter<T> {
   /**
    * The wrapped elements on that {@link #equals(Object)} and
    * {@link #hashCode()} is reset to default Java implementation.
    */
   private T wrappedElement;

   /**
    * Constructor
    * @param wrappedElement the wrapped elements on that {@link #equals(Object)} and {@link #hashCode()} is reset to default Java implementation.
    */
   public EqualsHashCodeResetter(T wrappedElement) {
      super();
      this.wrappedElement = wrappedElement;
   }

   /**
    * Overwritten to restore default Java implementation with reference based equality.
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof EqualsHashCodeResetter<?>) {
         return getWrappedElement() == ((EqualsHashCodeResetter<?>)obj).getWrappedElement();
      }
      else {
         return false;
      }
   }

   /**
    * Overwritten to restore default Java implementation with reference based equality.
    */
   @Override
   public int hashCode() {
      return System.identityHashCode(getWrappedElement());
   }

   /**
    * Returns the wrapped elements on that {@link #equals(Object)} and
    * {@link #hashCode()} is reset to default Java implementation.
    * @return The wrapped element.
    */
   public T getWrappedElement() {
      return wrappedElement;
   }
}