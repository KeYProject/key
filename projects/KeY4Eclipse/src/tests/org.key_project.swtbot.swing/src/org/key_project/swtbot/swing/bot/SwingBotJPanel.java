package org.key_project.swtbot.swing.bot;

import java.awt.Component;

import javax.swing.JPanel;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;

/**
 * <p>
 * This represents a {@link JPanel} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotButton}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJPanel extends AbstractSwingBotComponent<JPanel> {
   /**
    * Constructs an instance of this object with the given {@link JPanel}.
    * @param component The given {@link JPanel}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */      
   public SwingBotJPanel(JPanel component) throws WidgetNotFoundException {
      super(component);
   }
}
