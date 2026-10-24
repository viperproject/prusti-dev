// Populate the sidebar
//
// This is a script, and not included directly in the page, to control the total size of the book.
// The TOC contains an entry for each page, so if each page includes a copy of the TOC,
// the total size of the page becomes O(n**2).
class MDBookSidebarScrollbox extends HTMLElement {
    constructor() {
        super();
    }
    connectedCallback() {
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><a href="intro.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded "><a href="install.html"><strong aria-hidden="true">2.</strong> Installation</a></li><li class="chapter-item expanded "><a href="basic.html"><strong aria-hidden="true">3.</strong> Basic Usage</a></li><li class="chapter-item expanded "><a href="tour/summary.html"><strong aria-hidden="true">4.</strong> Guided Tour</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="tour/setup.html"><strong aria-hidden="true">4.1.</strong> Setup</a></li><li class="chapter-item expanded "><a href="tour/getting-started.html"><strong aria-hidden="true">4.2.</strong> Getting Started</a></li><li class="chapter-item expanded "><a href="tour/new.html"><strong aria-hidden="true">4.3.</strong> New</a></li><li class="chapter-item expanded "><a href="tour/push.html"><strong aria-hidden="true">4.4.</strong> Push</a></li><li class="chapter-item expanded "><a href="tour/pop.html"><strong aria-hidden="true">4.5.</strong> Pop</a></li><li class="chapter-item expanded "><a href="tour/testing.html"><strong aria-hidden="true">4.6.</strong> Testing</a></li><li class="chapter-item expanded "><a href="tour/option.html"><strong aria-hidden="true">4.7.</strong> Option</a></li><li class="chapter-item expanded "><a href="tour/generics.html"><strong aria-hidden="true">4.8.</strong> Generics</a></li><li class="chapter-item expanded "><a href="tour/peek.html"><strong aria-hidden="true">4.9.</strong> Peek</a></li><li class="chapter-item expanded "><a href="tour/pledges.html"><strong aria-hidden="true">4.10.</strong> Pledges (mutable peek)</a></li><li class="chapter-item expanded "><a href="tour/final.html"><strong aria-hidden="true">4.11.</strong> Final Code</a></li><li class="chapter-item expanded "><a href="tour/loop_invariants.html"><strong aria-hidden="true">4.12.</strong> Loop Invariants</a></li><li class="chapter-item expanded "><a href="tour/counterexamples.html"><strong aria-hidden="true">4.13.</strong> Counterexamples</a></li></ol></li><li class="chapter-item expanded "><a href="verify/summary.html"><strong aria-hidden="true">5.</strong> Verification Features</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="verify/panic.html"><strong aria-hidden="true">5.1.</strong> Absence of panics</a></li><li class="chapter-item expanded "><a href="verify/overflow.html"><strong aria-hidden="true">5.2.</strong> Overflow checks</a></li><li class="chapter-item expanded "><a href="verify/prepost.html"><strong aria-hidden="true">5.3.</strong> Pre- and postconditions</a></li><li class="chapter-item expanded "><a href="verify/assert_refute_assume.html"><strong aria-hidden="true">5.4.</strong> Assertions, refutations and assumptions</a></li><li class="chapter-item expanded "><a href="verify/trusted.html"><strong aria-hidden="true">5.5.</strong> Trusted functions</a></li><li class="chapter-item expanded "><a href="verify/pure.html"><strong aria-hidden="true">5.6.</strong> Pure functions</a></li><li class="chapter-item expanded "><a href="verify/predicate.html"><strong aria-hidden="true">5.7.</strong> Predicates</a></li><li class="chapter-item expanded "><a href="verify/external.html"><strong aria-hidden="true">5.8.</strong> External specifications</a></li><li class="chapter-item expanded "><a href="verify/loop.html"><strong aria-hidden="true">5.9.</strong> Loop body invariants</a></li><li class="chapter-item expanded "><a href="verify/pledge.html"><strong aria-hidden="true">5.10.</strong> Pledges</a></li><li class="chapter-item expanded "><a href="verify/type_cond_spec.html"><strong aria-hidden="true">5.11.</strong> Type-conditional spec refinements</a></li><li class="chapter-item expanded "><a href="verify/closure.html"><strong aria-hidden="true">5.12.</strong> Closures</a></li><li class="chapter-item expanded "><a href="verify/spec_ent.html"><strong aria-hidden="true">5.13.</strong> Specification entailments</a></li><li class="chapter-item expanded "><a href="verify/type-models.html"><strong aria-hidden="true">5.14.</strong> Type models</a></li><li class="chapter-item expanded "><a href="verify/counterexample.html"><strong aria-hidden="true">5.15.</strong> Counterexamples</a></li><li class="chapter-item expanded "><a href="verify/impl_block_specs.html"><strong aria-hidden="true">5.16.</strong> Specifications in trait impl blocks</a></li></ol></li><li class="chapter-item expanded "><a href="syntax.html"><strong aria-hidden="true">6.</strong> Specification Syntax</a></li></ol>';
        // Set the current, active page, and reveal it if it's hidden
        let current_page = document.location.href.toString().split("#")[0].split("?")[0];
        if (current_page.endsWith("/")) {
            current_page += "index.html";
        }
        var links = Array.prototype.slice.call(this.querySelectorAll("a"));
        var l = links.length;
        for (var i = 0; i < l; ++i) {
            var link = links[i];
            var href = link.getAttribute("href");
            if (href && !href.startsWith("#") && !/^(?:[a-z+]+:)?\/\//.test(href)) {
                link.href = path_to_root + href;
            }
            // The "index" page is supposed to alias the first chapter in the book.
            if (link.href === current_page || (i === 0 && path_to_root === "" && current_page.endsWith("/index.html"))) {
                link.classList.add("active");
                var parent = link.parentElement;
                if (parent && parent.classList.contains("chapter-item")) {
                    parent.classList.add("expanded");
                }
                while (parent) {
                    if (parent.tagName === "LI" && parent.previousElementSibling) {
                        if (parent.previousElementSibling.classList.contains("chapter-item")) {
                            parent.previousElementSibling.classList.add("expanded");
                        }
                    }
                    parent = parent.parentElement;
                }
            }
        }
        // Track and set sidebar scroll position
        this.addEventListener('click', function(e) {
            if (e.target.tagName === 'A') {
                sessionStorage.setItem('sidebar-scroll', this.scrollTop);
            }
        }, { passive: true });
        var sidebarScrollTop = sessionStorage.getItem('sidebar-scroll');
        sessionStorage.removeItem('sidebar-scroll');
        if (sidebarScrollTop) {
            // preserve sidebar scroll position when navigating via links within sidebar
            this.scrollTop = sidebarScrollTop;
        } else {
            // scroll sidebar to current active section when navigating via "next/previous chapter" buttons
            var activeSection = document.querySelector('#sidebar .active');
            if (activeSection) {
                activeSection.scrollIntoView({ block: 'center' });
            }
        }
        // Toggle buttons
        var sidebarAnchorToggles = document.querySelectorAll('#sidebar a.toggle');
        function toggleSection(ev) {
            ev.currentTarget.parentElement.classList.toggle('expanded');
        }
        Array.from(sidebarAnchorToggles).forEach(function (el) {
            el.addEventListener('click', toggleSection);
        });
    }
}
window.customElements.define("mdbook-sidebar-scrollbox", MDBookSidebarScrollbox);
