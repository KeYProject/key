package org.key_project.swtbot.swing.bot;

import java.awt.Component;

import javax.swing.JMenuItem;

import org.eclipse.swtbot.swt.finder.exceptions.WidgetNotFoundException;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotMenu;

/**
 * <p>
 * This represents a {@link JMenuItem} {@link Component}.
 * </p>
 * <p>
 * The class structure (attributes, methods, visibilities, ...) is oriented
 * on the implementation of {@link SWTBotMenu}.
 * </p>
 * @author Martin Hentschel
 */
public class SwingBotJMenuItem extends AbstractSwingBotButtonComponent<JMenuItem> {
   /**
    * Constructs an instance of this object with the given {@link JMenuItem}.
    * @param component The given {@link JMenuItem}.
    * @throws WidgetNotFoundException Is thrown when the given {@link Component} is {@code null}.
    */      
   public SwingBotJMenuItem(JMenuItem component) throws WidgetNotFoundException {
      super(component);
   }
}
