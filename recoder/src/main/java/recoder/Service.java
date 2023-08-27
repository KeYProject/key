/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

/**
 * Primary RECODER service interface.
 */
public interface Service {

    /**
     * Called by the service configuration indicating that all services are known. Services may now
     * start communicating or linking among their configuration partners. The service configuration
     * can be memorized if it has not been passed in by a constructor already.
     *
     * @param cfg the service configuration this services has been assigned to.
     */
    void initialize(ServiceConfiguration cfg);

    /**
     * Returns the service configuration this service is a part of.
     *
     * @return the configuration of this service.
     */
    ServiceConfiguration getServiceConfiguration();

}
