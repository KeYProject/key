package de.uka.ilkd.key.gui.configuration;

import java.util.LinkedList;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.GUIEvent;
import de.uka.ilkd.key.logic.ITermLabel;
import de.uka.ilkd.key.rule.ITermLabelWorker;
import de.uka.ilkd.key.rule.TermLabelWorkerManagement;

/**
 * Provides all settings in context of term labels ({@link ITermLabel}).
 * @author Martin Hentschel
 */
public class LabelSettings implements Settings, Cloneable {
   /**
    * The key used in a {@link Properties} instance to save {@link #getLabelInstantiators()}.
    */
   private static final String LABEL_INSTANTIATORS_KEY = "[Label]Instantiators";

   /**
    * Contains all listeners to inform when something changes.
    */
   private List<SettingsListener> listeners = new LinkedList<SettingsListener>();

   /**
    * The {@link ITermLabelWorker} to use when rules are applied during proof.
    */
   private ImmutableList<ITermLabelWorker> labelInstantiators = ImmutableSLList.<ITermLabelWorker>nil();
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void readSettings(Object sender, Properties props) {
      String instantiatorsValue = props.getProperty(LABEL_INSTANTIATORS_KEY);
      if (instantiatorsValue != null) {
         String[] instantiators = instantiatorsValue.split(",");
         ImmutableList<ITermLabelWorker> loadedInstantiators = ImmutableSLList.<ITermLabelWorker>nil();
         for (String instantiator : instantiators) {
            ITermLabelWorker instance = TermLabelWorkerManagement.getInstantiator(instantiator.trim());
            if (instance != null) {
               loadedInstantiators = loadedInstantiators.append(instance);
            }
         }
         labelInstantiators = loadedInstantiators;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void writeSettings(Object sender, Properties props) {
      StringBuffer instantiators = new StringBuffer();
      boolean afterFirst = false;
      for (ITermLabelWorker instantiator : labelInstantiators) {
         if (afterFirst) {
            instantiators.append(", ");
         }
         else {
            afterFirst = true;
         }
         instantiators.append(instantiator.getName());
      }
      props.setProperty(LABEL_INSTANTIATORS_KEY, instantiators.toString());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addSettingsListener(SettingsListener l) {
      if (l != null) {
         listeners.add(l);
      }
   }
   
   /**
    * Returns the {@link ITermLabelWorker}s to use when a rule is applied.
    * @return The {@link ITermLabelWorker}s to use when a rule is applied.
    */
   public ImmutableList<ITermLabelWorker> getLabelInstantiators() {
      return labelInstantiators;
   }

   /**
    * Sets the {@link ITermLabelWorker}s to use when a rule is applied.
    * @param labelInstantiators The {@link ITermLabelWorker}s to use when a rule is applied.
    */
   public void setLabelInstantiators(ImmutableList<ITermLabelWorker> labelInstantiators) {
      if (labelInstantiators != null) {
         this.labelInstantiators = labelInstantiators;
      }
      else {
         this.labelInstantiators = ImmutableSLList.<ITermLabelWorker>nil();
      }
      fireSettingsChanged();
   }
   
   /** 
    * Sends the message that the state of this setting has been
    * changed to its registered listeners (not thread-safe).
    */
   protected void fireSettingsChanged() {
      for (SettingsListener aListenerList : listeners) {
         aListenerList.settingsChanged(new GUIEvent(this));
      }
   }
}
