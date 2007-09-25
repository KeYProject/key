# This file is part of KeY - Integrated Deductive Software Design
# Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
#                         Universitaet Koblenz-Landau, Germany
#                         Chalmers University of Technology, Sweden
#
# The KeY system is protected by the GNU General Public License.
# See LICENSE.TXT for details.

# Which eclipse version do we use ?
# Set to 3.1 if not provided by user
ECLIPSE_VERSION ?= 3.1

# Which build.xml to use is dependant on the eclipse version
# since there are hard-coded version numbers in there
BUILD_FILE=build-$(ECLIPSE_VERSION).xml

# Set windowing system to be used, normally gtk.
# Needed since the swt libraries are specific to the underlying
# windowing system
WS=gtk

# enable verbose ant outputs by commenting out the following line
#VERBOSE=-verbose

.PHONY: export

export: 
ifdef ECLIPSE_HOME
	java -cp $(ECLIPSE_HOME)/startup.jar org.eclipse.core.launcher.Main \
	-application org.eclipse.ant.core.antRunner -buildfile $(BUILD_FILE) \
	-Declipse_home=$(ECLIPSE_HOME) -Dws=$(WS) $(VERBOSE) clean zip.plugin
	rm -rf workspace
else
	@echo
	@echo "!! Environment variable ECLIPSE_HOME not specified !!"
	@echo "Point this to the base of your eclipse installation to build"
	@echo "the plug-in."
	@echo "As default eclipse version 3.1 is assumed. When using 3.0.2"
	@echo "additionally specify ECLIPSE_VERSION=3.0.2"
	@echo "example: ECLIPSE_HOME=/home/myself/eclipse-3.0.2"
	@echo "    ECLIPSE_VERSION=3.0.2 make"
	@echo
endif

clean:
	rm -f KeYPlugIn.jar KeYPlugInsrc.zip KeYPlugin_*.zip
	rm -rf workspace
