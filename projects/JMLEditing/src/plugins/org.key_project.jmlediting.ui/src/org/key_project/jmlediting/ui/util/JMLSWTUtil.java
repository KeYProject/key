package org.key_project.jmlediting.ui.util;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.swt.widgets.Combo;
import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;

public class JMLSWTUtil {
   public static void fillComboWithParentProfilesAndDate(final Combo combo) {
      final List<IJMLProfile> allProfiles = JMLProfileManagement.instance()
            .getAvailableProfilesSortedByName();

      final List<String> result = new ArrayList<String>();

      final Iterator<IJMLProfile> iterator = allProfiles.iterator();
      while (iterator.hasNext()) {
         final IJMLProfile profile = iterator.next();
         if (!(profile instanceof IDerivedProfile)) {
            result.add(profile.getName());
            combo.setData(profile.getName(), profile);
         }
      }

      combo.setItems(result.toArray(new String[result.size()]));
   }
}
