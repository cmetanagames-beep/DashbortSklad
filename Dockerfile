FROM node:20-bookworm-slim

WORKDIR /app

COPY package.json ./
RUN npm install --omit=dev

COPY . .

ENV NODE_ENV=production \
    HOST=0.0.0.0 \
    PORT=8787 \
    AKFIX_DATA_DIR=/app/data

RUN mkdir -p /app/data

VOLUME ["/app/data"]
EXPOSE 8787

HEALTHCHECK --interval=30s --timeout=5s --start-period=20s --retries=3 \
  CMD node -e "fetch('http://127.0.0.1:'+(process.env.PORT||8787)+'/api/health').then(r=>{if(!r.ok)process.exit(1)}).catch(()=>process.exit(1))"

CMD ["npm", "start"]
