/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.example.action;

import java.util.Properties;

import org.eclipse.ui.internal.intro.impl.IntroPlugin;
import org.eclipse.ui.intro.IIntroSite;
import org.eclipse.ui.intro.config.IIntroAction;

import de.hentschel.visualdbc.example.wizard.KeyQuicktourWizard;

/**
 * An intro action that opens the {@link KeyQuicktourWizard}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeyQuicktourWizardIntroAction implements IIntroAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IIntroSite site, Properties params) {
      IntroPlugin.closeIntro();
      KeyQuicktourWizard.openWizard(site.getShell());
   }
}
