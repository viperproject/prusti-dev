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
        this.innerHTML = '<ol class="chapter"><li class="chapter-item expanded "><a href="intro.html"><strong aria-hidden="true">1.</strong> Introduction</a></li><li class="chapter-item expanded "><a href="config/summary.html"><strong aria-hidden="true">2.</strong> Configuration</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="config/providing.html"><strong aria-hidden="true">2.1.</strong> Providing Flags</a></li><li class="chapter-item expanded "><a href="config/flags.html"><strong aria-hidden="true">2.2.</strong> List of Configuration Flags</a></li></ol></li><li class="chapter-item expanded "><a href="pipeline/summary.html"><strong aria-hidden="true">3.</strong> Verification Pipeline</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="pipeline/binary.html"><strong aria-hidden="true">3.1.</strong> Binary stage</a></li><li class="chapter-item expanded "><a href="pipeline/rust.html"><strong aria-hidden="true">3.2.</strong> Rust compilation stage</a></li><li class="chapter-item expanded "><a href="pipeline/prusti.html"><strong aria-hidden="true">3.3.</strong> Prusti processing stage</a></li><li class="chapter-item expanded "><a href="pipeline/viper.html"><strong aria-hidden="true">3.4.</strong> Viper verification stage</a></li><li class="chapter-item expanded "><a href="pipeline/report.html"><strong aria-hidden="true">3.5.</strong> Reporting stage</a></li></ol></li><li class="chapter-item expanded "><a href="macros.html"><strong aria-hidden="true">4.</strong> Macros</a></li><li class="chapter-item expanded "><a href="encoding/summary.html"><strong aria-hidden="true">5.</strong> Viper Encoding</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="encoding/types.html"><strong aria-hidden="true">5.1.</strong> Types</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="encoding/types-heap.html"><strong aria-hidden="true">5.1.1.</strong> Heap-based type encoding</a></li><li class="chapter-item expanded "><a href="encoding/types-snap.html"><strong aria-hidden="true">5.1.2.</strong> Snapshot-based type encoding</a></li></ol></li><li class="chapter-item expanded "><a href="encoding/pure.html"><strong aria-hidden="true">5.2.</strong> Pure function encoding</a></li><li class="chapter-item expanded "><a href="encoding/mangling.html"><strong aria-hidden="true">5.3.</strong> Name mangling</a></li></ol></li><li class="chapter-item expanded "><a href="layout.html"><strong aria-hidden="true">6.</strong> Repository Layout</a></li><li class="chapter-item expanded "><a href="development/summary.html"><strong aria-hidden="true">7.</strong> Development</a></li><li><ol class="section"><li class="chapter-item expanded "><a href="development/setup.html"><strong aria-hidden="true">7.1.</strong> Setup</a></li><li class="chapter-item expanded "><a href="development/build.html"><strong aria-hidden="true">7.2.</strong> Building</a></li><li class="chapter-item expanded "><a href="development/tests.html"><strong aria-hidden="true">7.3.</strong> Tests</a></li><li class="chapter-item expanded "><a href="development/ide.html"><strong aria-hidden="true">7.4.</strong> IDE integration</a></li><li class="chapter-item expanded "><a href="development/debug.html"><strong aria-hidden="true">7.5.</strong> Debugging</a></li></ol></li></ol>';
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
