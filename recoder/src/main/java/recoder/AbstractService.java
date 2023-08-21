/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

public abstract class AbstractService implements Service {

    protected ServiceConfiguration serviceConfiguration;

    /**
     * Constructs a service without configuration. Be cautious when doing so.
     */
    protected AbstractService() {
        super();
    }

    protected AbstractService(ServiceConfiguration config) {
        if (config == null) {
            throw new NullPointerException("No service configuration given");
        }
        this.serviceConfiguration = config;
    }

    /**
     * Called by the service configuration indicating that all services are known. Services may now
     * start communicating or linking among their configuration partners. The service configuration
     * can be memorized if it has not been passed in by a constructor already. The default
     * implementation does nothing.
     *
     * @param cfg the service configuration this services has been assigned to.
     */
    @SuppressWarnings("all")
    public void initialize(ServiceConfiguration cfg) {
    }

    public ServiceConfiguration getServiceConfiguration() {
        return serviceConfiguration;
    }
}
