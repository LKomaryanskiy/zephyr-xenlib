/* SPDX-License-Identifier: Apache-2.0 */
/*
 * Copyright (c) 2023 EPAM Systems
 */

#ifndef XENLIB_XEN_SHELL_H
#define XENLIB_XEN_SHELL_H

/*
 * Start console thread in dom0, that reads domain output.
 *
 * @param domain - domain, where console thread will be started
 *
 * @return - zero on success, negative errno on failure
 */
int start_domain_console(struct xen_domain *domain);

/*
 * Stop console thread in dom0, that reads domain output.
 *
 * @param domain - domain, where console thread will be stopped
 *
 * @return - zero on success, negative errno on failure
 */
int stop_domain_console(struct xen_domain *domain);

#endif /* XENLIB_XEN_SHELL_H */
