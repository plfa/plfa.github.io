function darkmode(lightId, darkId) {
  const stylesheetLight = document.getElementById(lightId);
  const stylesheetDark = document.getElementById(darkId);
  // Function to update the URL.search attribute in all anchors
  const updateAnchors = function (enabled) {

  };
  // Function to set darkmode in document
  const set = function (enabled) {
    window.darkmode.enabled = enabled;
    // Set 'dark' parameter on internal anchor links
    const base = window.location.protocol + window.location.host;
    const anchors = document.getElementsByTagName("a");
    for (var i = 0; i < anchors.length; i++) {
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
    // Set or remove 'disabled' attribute on stylesheets
    if (enabled) {
      stylesheetDark.disabled = false;
      stylesheetLight.disabled = true;
    } else {
      stylesheetLight.disabled = false;
      stylesheetDark.disabled = true;
    }
  };
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
