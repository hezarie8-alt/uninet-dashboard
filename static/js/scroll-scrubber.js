function colorWithAlpha(color, alpha) {
    const value = String(color || '').trim();
    const hex = value.replace('#', '');
    if (!/^[0-9a-f]{3}$|^[0-9a-f]{6}$/i.test(hex)) return value;
    const normalized = hex.length === 3 ? hex.split('').map(part => part + part).join('') : hex;
    const red = parseInt(normalized.slice(0, 2), 16);
    const green = parseInt(normalized.slice(2, 4), 16);
    const blue = parseInt(normalized.slice(4, 6), 16);
    return `rgba(${red},${green},${blue},${alpha})`;
}

class ScrollScrubber {
    constructor(canvasId, options = {}) {
        this.canvas = document.getElementById(canvasId);
        if (!this.canvas) return;
        this.ctx = this.canvas.getContext('2d');
        const styles = getComputedStyle(document.documentElement);
        const token = name => styles.getPropertyValue(name).trim();
        this.options = {
            particleCount: 80,
            gradientColors: [token('--brand-strong'), token('--brand'), token('--accent')],
            reducedMotion: window.matchMedia('(prefers-reduced-motion: reduce)').matches,
            ...options
        };
        this.progress = 0;
        this.particles = [];
        this.animationId = null;
        this.isInView = false;
        this.resizeObserver = null;
        this._init();
    }

    _init() {
        this._resize();
        this._createParticles();
        this.resizeObserver = new ResizeObserver(() => this._resize());
        this.resizeObserver.observe(this.canvas.parentElement || this.canvas);
    }

    _resize() {
        const parent = this.canvas.parentElement || document.body;
        const rect = parent.getBoundingClientRect();
        const dpr = Math.min(window.devicePixelRatio || 1, 2);
        this.canvas.width = rect.width * dpr;
        this.canvas.height = rect.height * dpr;
        this.ctx.scale(dpr, dpr);
        this.width = rect.width;
        this.height = rect.height;
    }

    _createParticles() {
        this.particles = [];
        for (let i = 0; i < this.options.particleCount; i++) {
            this.particles.push({
                x: Math.random(),
                y: Math.random(),
                size: Math.random() * 3 + 1,
                speedX: (Math.random() - 0.5) * 0.002,
                speedY: (Math.random() - 0.5) * 0.002,
                opacity: Math.random() * 0.5 + 0.1,
                hue: Math.random() * 60 + 170
            });
        }
    }

    setProgress(progress) {
        this.progress = Math.max(0, Math.min(1, progress));
        if (!this.animationId && this.isInView) {
            this._animate();
        }
    }

    start() {
        this.isInView = true;
        if (!this.animationId) this._animate();
    }

    stop() {
        this.isInView = false;
        if (this.animationId) {
            cancelAnimationFrame(this.animationId);
            this.animationId = null;
        }
    }

    _animate() {
        if (this.options.reducedMotion) {
            this._drawStatic();
            return;
        }
        this._draw();
        this.animationId = requestAnimationFrame(() => this._animate());
    }

    _draw() {
        const ctx = this.ctx;
        const w = this.width;
        const h = this.height;
        const p = this.progress;

        // Clear
        ctx.clearRect(0, 0, w, h);

        // Background gradient shifts with scroll
        const gradAngle = p * Math.PI * 2;
        const gx1 = w * 0.5 + Math.cos(gradAngle) * w * 0.5;
        const gy1 = h * 0.5 + Math.sin(gradAngle) * h * 0.5;
        const gx2 = w * 0.5 - Math.cos(gradAngle) * w * 0.5;
        const gy2 = h * 0.5 - Math.sin(gradAngle) * h * 0.5;

        const bgGrad = ctx.createLinearGradient(gx1, gy1, gx2, gy2);
        const alpha = 0.15 + p * 0.1;
        const colors = this.options.gradientColors;
        bgGrad.addColorStop(0, colorWithAlpha(colors[0], alpha));
        bgGrad.addColorStop(0.5, colorWithAlpha(colors[2], alpha * 0.7));
        bgGrad.addColorStop(1, colorWithAlpha(colors[1], alpha * 0.5));
        ctx.fillStyle = bgGrad;
        ctx.fillRect(0, 0, w, h);

        // Central glow orb
        const orbX = w * 0.5 + Math.cos(p * Math.PI * 1.5) * w * 0.15;
        const orbY = h * 0.5 + Math.sin(p * Math.PI * 2) * h * 0.1;
        const orbRadius = Math.min(w, h) * (0.2 + p * 0.15);
        const orbGrad = ctx.createRadialGradient(orbX, orbY, 0, orbX, orbY, orbRadius);
        orbGrad.addColorStop(0, colorWithAlpha(colors[1], 0.25 + p * 0.15));
        orbGrad.addColorStop(0.6, colorWithAlpha(colors[2], 0.1 + p * 0.08));
        orbGrad.addColorStop(1, 'rgba(0,0,0,0)');
        ctx.fillStyle = orbGrad;
        ctx.fillRect(0, 0, w, h);

        // Particles
        for (const particle of this.particles) {
            particle.x += particle.speedX;
            particle.y += particle.speedY;
            if (particle.x < 0 || particle.x > 1) particle.speedX *= -1;
            if (particle.y < 0 || particle.y > 1) particle.speedY *= -1;

            const px = particle.x * w;
            const py = particle.y * h;
            const size = particle.size * (1 + p * 0.5);
            const opacity = particle.opacity * (0.5 + p * 0.5);

            ctx.beginPath();
            ctx.arc(px, py, size, 0, Math.PI * 2);
            ctx.fillStyle = `hsla(${particle.hue + p * 40}, 70%, 60%, ${opacity})`;
            ctx.fill();
        }

        // Connection lines between nearby particles (progressive)
        if (p > 0.2) {
            const lineOpacity = (p - 0.2) * 0.3;
            ctx.strokeStyle = colorWithAlpha(colors[1], lineOpacity);
            ctx.lineWidth = 0.5;
            for (let i = 0; i < this.particles.length; i++) {
                for (let j = i + 1; j < this.particles.length; j++) {
                    const dx = (this.particles[i].x - this.particles[j].x) * w;
                    const dy = (this.particles[i].y - this.particles[j].y) * h;
                    const dist = Math.sqrt(dx * dx + dy * dy);
                    if (dist < 120) {
                        ctx.beginPath();
                        ctx.moveTo(this.particles[i].x * w, this.particles[i].y * h);
                        ctx.lineTo(this.particles[j].x * w, this.particles[j].y * h);
                        ctx.globalAlpha = (1 - dist / 120) * lineOpacity;
                        ctx.stroke();
                        ctx.globalAlpha = 1;
                    }
                }
            }
        }
    }

    _drawStatic() {
        const ctx = this.ctx;
        const w = this.width;
        const h = this.height;
        ctx.clearRect(0, 0, w, h);

        const bgGrad = ctx.createLinearGradient(0, 0, w, h);
        const colors = this.options.gradientColors;
        bgGrad.addColorStop(0, colorWithAlpha(colors[0], 0.15));
        bgGrad.addColorStop(0.5, colorWithAlpha(colors[2], 0.1));
        bgGrad.addColorStop(1, colorWithAlpha(colors[1], 0.08));
        ctx.fillStyle = bgGrad;
        ctx.fillRect(0, 0, w, h);

        for (const particle of this.particles) {
            ctx.beginPath();
            ctx.arc(particle.x * w, particle.y * h, particle.size, 0, Math.PI * 2);
            ctx.fillStyle = `hsla(${particle.hue}, 70%, 60%, ${particle.opacity * 0.5})`;
            ctx.fill();
        }
    }

    destroy() {
        this.stop();
        if (this.resizeObserver) this.resizeObserver.disconnect();
    }
}


/* ============================================================
   Scroll Manager — orchestrates all scroll-driven animations
   ============================================================ */

class ScrollManager {
    constructor() {
        this.scrubbers = [];
        this.scrollSections = [];
        this.progressBar = null;
        this.reducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
        this._init();
    }

    _init() {
        this._createProgressBar();
        this._initAboutScrollSection();
        this._initHomepageAnimations();
        this._initScrollProgress();
    }

    _createProgressBar() {
        this.progressBar = document.createElement('div');
        this.progressBar.className = 'scroll-progress-bar';
        document.body.prepend(this.progressBar);
    }

    _initScrollProgress() {
        const updateProgress = () => {
            const scrollTop = window.scrollY;
            const docHeight = document.documentElement.scrollHeight - window.innerHeight;
            const progress = docHeight > 0 ? (scrollTop / docHeight) * 100 : 0;
            if (this.progressBar) {
                this.progressBar.style.width = progress + '%';
            }
        };
        window.addEventListener('scroll', updateProgress, { passive: true });
        updateProgress();
    }

    _initAboutScrollSection() {
        const section = document.querySelector('.about-scroll-section');
        if (!section) return;

        const canvas = document.getElementById('scrollCanvas');
        if (canvas) {
            const scrubber = new ScrollScrubber('scrollCanvas');
            this.scrubbers.push(scrubber);

            const observer = new IntersectionObserver((entries) => {
                entries.forEach(entry => {
                    if (entry.isIntersecting) {
                        scrubber.start();
                    } else {
                        scrubber.stop();
                    }
                });
            }, { threshold: 0 });
            observer.observe(section);
        }

        const textItems = section.querySelectorAll('.scroll-text-item');
        const dots = section.querySelectorAll('.scroll-step-dot');
        const stepCount = textItems.length;

        const handleScroll = () => {
            const rect = section.getBoundingClientRect();
            const sectionHeight = section.offsetHeight - window.innerHeight;
            const scrolled = -rect.top;
            const progress = Math.max(0, Math.min(1, scrolled / sectionHeight));

            // Update canvas scrubber
            if (this.scrubbers.length > 0) {
                this.scrubbers[0].setProgress(progress);
            }

            // Update text items
            const stepSize = 1 / stepCount;
            const currentStep = Math.min(Math.floor(progress / stepSize), stepCount - 1);

            textItems.forEach((item, i) => {
                item.classList.toggle('active', i === currentStep);
            });

            dots.forEach((dot, i) => {
                dot.classList.toggle('active', i === currentStep);
            });
        };

        window.addEventListener('scroll', handleScroll, { passive: true });
        handleScroll();
    }

    _initHomepageAnimations() {
        // Staggered bento grid reveal — bidirectional
        const cards = document.querySelectorAll('.bento-grid .feature-card');
        if (cards.length > 0) {
            const observer = new IntersectionObserver((entries) => {
                entries.forEach(entry => {
                    entry.target.classList.toggle('revealed', entry.isIntersecting);
                });
            }, { threshold: 0.15 });
            cards.forEach(card => observer.observe(card));
        }

        // CTA section reveal — bidirectional
        const ctaGlass = document.querySelector('.cta-glass');
        if (ctaGlass) {
            const observer = new IntersectionObserver((entries) => {
                entries.forEach(entry => {
                    entry.target.classList.toggle('revealed', entry.isIntersecting);
                });
            }, { threshold: 0.2 });
            observer.observe(ctaGlass);
        }

        // Stats counter animation
        const statNums = document.querySelectorAll('.stat-num');
        if (statNums.length > 0) {
            const observer = new IntersectionObserver((entries) => {
                entries.forEach(entry => {
                    entry.target.classList.toggle('counting', entry.isIntersecting);
                });
            }, { threshold: 0.5 });
            statNums.forEach(el => observer.observe(el));
        }
    }

    destroy() {
        this.scrubbers.forEach(s => s.destroy());
    }
}


/* ============================================================
   Initialize on DOM ready
   ============================================================ */
document.addEventListener('DOMContentLoaded', () => {
    window.scrollManager = new ScrollManager();
});
