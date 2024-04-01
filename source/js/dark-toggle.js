const updateColor = (color) => {
    document
        .querySelectorAll("mjx-xypic-object")
        .forEach((el) => (el.style.color = color));
    document
        .querySelectorAll("mjx-math > mjx-xypic > svg > g")
        .forEach((el) => el.setAttribute("stroke", color));
};

document.addEventListener("DOMContentLoaded", () => {
    MathJax.startup.promise.then(() => {
        const initialColor = getComputedStyle(document.documentElement)
            .getPropertyValue("--svg-text")
            .trim();
        updateColor(initialColor);
    });
    let toggle = document.querySelector("dark-mode-toggle");
    toggle.addEventListener("colorschemechange", () => {
        toggle = document.querySelector("dark-mode-toggle");
        updateColor(toggle.mode === "dark" ? "#dcdcdc" : "#171717");
    });
});

window.matchMedia("(prefers-color-scheme: dark)").addListener((e) => {
    updateColor(e.matches ? "#dcdcdc" : "#171717");
});
