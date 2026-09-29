import { defineConfig } from "vite";
import react from "@vitejs/plugin-react";

const apiProxy = {
  "/api": {
    target: "http://127.0.0.1:8765",
    changeOrigin: true,
  },
};

export default defineConfig({
  plugins: [react()],
  server: { host: "127.0.0.1", port: 5173, strictPort: true, proxy: apiProxy },
  preview: { host: "127.0.0.1", port: 4173, strictPort: true, proxy: apiProxy },
});
