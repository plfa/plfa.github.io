function darkmode(lightId, darkId) {
  const stylesheetLight = document.getElementById(lightId);
  const stylesheetDark = document.getElementById(darkId);
  // Function to set darkmode in document
  const set = function (enabled) {
    window.darkmode.enabled = enabled;
    // Set 'dark' parameter on internal anchor links
    const base = window.location.protocol + window.location.host;
    const anchors = document.getElementsByTagName("a");
    for (var i = 0; i < anchors.length; i++) {
      if (anchors[i].hasAttribute('href')) {
        const url = new URL(anchors[i].href, base);
        if (url.host === window.location.host) {
          if (enabled) {
            url.searchParams.set('dark','true');
          }
          else {
            url.searchParams.delete('dark');
          }
          anchors[i].href = url.href;
        }
      }
    }
    // Set or remove 'disabled' attribute on stylesheets
    // Set the dark mode trigger
    const trigger = document.getElementById('darkmode-trigger');
    if (enabled) {
      stylesheetDark.disabled = false;
      trigger.classList.remove('fa-moon');
      stylesheetLight.disabled = true;
      trigger.classList.add('fa-sun');
    } else {
      stylesheetLight.disabled = false;
      trigger.classList.remove('fa-sun');
      stylesheetDark.disabled = true;
      trigger.classList.add('fa-moon');
    }
  };
  const anchors = document.getElementsByTagName("a");
  // Create top-level function to toggle dark mode
  window.darkmode.toggle = function () {
    set(!window.darkmode.enabled);
  };
  // Initialise darkmode
  const initialise = function () {
    const params = new URLSearchParams(window.location.search);
    const enabled = params.has("dark") && params.get("dark") == "true";
    set(enabled);
  };
  initialise();
}
