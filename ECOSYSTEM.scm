;; SPDX-License-Identifier: AGPL-3.0-or-later
;; SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell
;; ECOSYSTEM.scm — absolute-zero

(ecosystem
  (version "1.0.0")
  (name "absolute-zero")
  (type "project")
  (purpose "**Formal Verification of Certified Null Operations: When Doing Nothing Is Everything**")

  (position-in-ecosystem
    "Part of hyperpolymath ecosystem. Follows RSR guidelines.")

  (related-projects
    (project (name "rhodium-standard-repositories")
             (url "https://github.com/hyperpolymath/rhodium-standard-repositories")
             (relationship "standard")))

  (what-this-is "**Formal Verification of Certified Null Operations: When Doing Nothing Is Everything**")
  (what-this-is-not "- NOT exempt from RSR compliance"))
