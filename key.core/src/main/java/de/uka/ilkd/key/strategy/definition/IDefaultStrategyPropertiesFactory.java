// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.definition;

import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Instances of this factory are used to create default {@link StrategyProperties}
 * used by a {@link Strategy} defined via its {@link StrategySettingsDefinition}.
 * @author Martin Hentschel
 */
public interface IDefaultStrategyPropertiesFactory {
   /**
    * The default implementation.
    */
   public static IDefaultStrategyPropertiesFactory DEFAULT_FACTORY = new IDefaultStrategyPropertiesFactory() {
      @Override
      public StrategyProperties createDefaultStrategyProperties() {
         return new StrategyProperties();
      }
   };
   
   /**
    * Creates new default {@link StrategyProperties}.
    * @return The new default {@link StrategyProperties}.
    */
   public StrategyProperties createDefaultStrategyProperties();
}