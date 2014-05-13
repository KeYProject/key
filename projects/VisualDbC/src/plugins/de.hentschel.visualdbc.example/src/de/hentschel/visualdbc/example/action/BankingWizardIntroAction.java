/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package de.hentschel.visualdbc.example.action;

import java.util.Properties;

import org.eclipse.ui.internal.intro.impl.IntroPlugin;
import org.eclipse.ui.intro.IIntroSite;
import org.eclipse.ui.intro.config.IIntroAction;

import de.hentschel.visualdbc.example.wizard.BankingWizard;

/**
 * An intro action that opens the {@link BankingWizard}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class BankingWizardIntroAction implements IIntroAction {
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IIntroSite site, Properties params) {
      IntroPlugin.closeIntro();
      BankingWizard.openWizard(site.getShell());
   }
}